
# 从概念模型到工程实现：Rust语言视角下的分层架构与技术映射

## 目录

- [从概念模型到工程实现：Rust语言视角下的分层架构与技术映射](#从概念模型到工程实现rust语言视角下的分层架构与技术映射)
  - [目录](#目录)
  - [1. 引言：软件设计的核心挑战](#1-引言软件设计的核心挑战)
    - [业务复杂性与技术复杂性的双重挑战](#业务复杂性与技术复杂性的双重挑战)
    - [为什么选择Rust](#为什么选择rust)
    - [本文结构与学习路径](#本文结构与学习路径)
  - [2. 概念模型与领域驱动设计](#2-概念模型与领域驱动设计)
    - [什么是概念模型](#什么是概念模型)
    - [领域驱动设计核心概念](#领域驱动设计核心概念)
    - [Rust与DDD的亲和性](#rust与ddd的亲和性)
  - [3. 从概念到代码：Rust类型系统映射](#3-从概念到代码rust类型系统映射)
    - [实体与值对象的映射](#实体与值对象的映射)
    - [聚合与边界的表达](#聚合与边界的表达)
    - [关系映射的策略](#关系映射的策略)
    - [领域规则与不变量实现](#领域规则与不变量实现)
    - [Rust类型映射的优劣分析](#rust类型映射的优劣分析)
  - [4. 动态行为建模：从状态到算法](#4-动态行为建模从状态到算法)
    - [状态机模式实现](#状态机模式实现)
    - [业务过程与领域服务](#业务过程与领域服务)
    - [领域事件与事件处理](#领域事件与事件处理)
    - [异步编程模型与领域逻辑](#异步编程模型与领域逻辑)
    - [行为验证与形式化方法](#行为验证与形式化方法)
  - [5. 分层架构：关注点分离的工程实践](#5-分层架构关注点分离的工程实践)
    - [整洁架构与端口适配器模式](#整洁架构与端口适配器模式)
    - [领域层：业务核心的纯粹表达](#领域层业务核心的纯粹表达)
    - [应用层：用例协调与业务流程](#应用层用例协调与业务流程)
    - [基础设施层：技术关注点封装](#基础设施层技术关注点封装)
  - [6. Rust技术栈选型与应用](#6-rust技术栈选型与应用)
    - [领域层技术选择](#领域层技术选择)
    - [应用层技术选择](#应用层技术选择)
    - [基础设施层技术栈全景](#基础设施层技术栈全景)
      - [异步运行时与并发](#异步运行时与并发)
      - [数据持久化方案](#数据持久化方案)
      - [Web与网络框架](#web与网络框架)
      - [序列化与通信](#序列化与通信)
      - [配置与日志](#配置与日志)
  - [7. 高级架构模式与Rust实现](#7-高级架构模式与rust实现)
    - [CQRS模式](#cqrs模式)
    - [事件溯源](#事件溯源)
    - [微服务架构](#微服务架构)
    - [分布式事务处理](#分布式事务处理)
  - [8. 工程实践案例](#8-工程实践案例)
    - [电子商务系统示例](#电子商务系统示例)
    - [实时库存管理系统](#实时库存管理系统)
    - [事件驱动微服务架构](#事件驱动微服务架构)
  - [9. 工程化最佳实践](#9-工程化最佳实践)
    - [测试策略](#测试策略)
    - [CI/CD 配置示例](#cicd-配置示例)
    - [Dockerfile示例](#dockerfile示例)
    - [监控与可观测性配置](#监控与可观测性配置)
    - [自动化容量测试](#自动化容量测试)
  - [10. 总结与展望](#10-总结与展望)
    - [未来展望](#未来展望)
  - [思维导图](#思维导图)

## 1. 引言：软件设计的核心挑战

### 业务复杂性与技术复杂性的双重挑战

现代软件开发面临两大核心挑战：业务复杂性和技术复杂性。业务复杂性来源于现实世界问题的内在复杂性，包括领域规则、业务流程和状态变化；技术复杂性则来自于实现软件所使用的工具、平台和方法。

成功的软件设计需要同时应对这两种复杂性，既能准确表达业务领域知识，又能合理利用技术手段实现可靠、高效的系统。关键挑战在于：如何在业务逻辑与技术细节之间建立清晰的界限和有效的映射关系。

### 为什么选择Rust

Rust语言在解决这一挑战上具有独特优势：

1. **强大的类型系统**：能够精确建模领域概念和关系，在编译时捕获大量错误。
2. **所有权模型**：提供内存安全保证，无需垃圾回收，适合构建高性能系统。
3. **trait与泛型**：提供灵活的抽象机制，支持接口设计和依赖反转。
4. **模块系统**：提供良好的封装和可见性控制，支持关注点分离。
5. **零成本抽象**：允许高层抽象而不牺牲性能，减轻了抽象惩罚。

这些特性使Rust成为连接业务复杂性和技术复杂性的理想桥梁，能够既表达丰富的业务模型，又满足技术性能和安全要求。

### 本文结构与学习路径

本文提供了从概念到实践的完整视角，适合不同层次的读者：

- **领域建模初学者**：建议从第2章开始，了解概念模型和DDD基础。
- **Rust开发者**：可重点关注第3、4章，了解如何利用Rust特性表达业务概念。
- **架构师**：第5、6、7章探讨了架构设计和技术选型的关键决策。
- **项目负责人**：第8、9章提供了实战案例和工程实践策略。

## 2. 概念模型与领域驱动设计

### 什么是概念模型

概念模型是对特定领域或问题空间中关键概念及其关系的抽象表示。它是业务专家、分析师和开发者之间的共享语言，服务于两个关键目的：

1. 作为沟通工具，帮助所有利益相关者达成对业务领域的共识
2. 作为设计蓝图，指导软件实现的组织和结构

良好的概念模型具有以下特征：

- 反映领域专家的心智模型
- 关注本质概念，忽略技术细节
- 明确界定概念边界和关系
- 表达领域中的不变规则和约束

### 领域驱动设计核心概念

领域驱动设计(Domain-Driven Design, DDD)提供了一套将概念模型转化为软件设计的方法论，其核心概念包括：

1. **实体(Entity)**：具有连续性标识的对象，即使其属性变化，依然被视为同一对象。

   ```rust
   pub struct User {
       id: UserId,
       name: String,
       email: Email,
       // 其他属性
   }
   ```

2. **值对象(Value Object)**：通过其属性集合定义的对象，没有标识，不可变。

   ```rust
   #[derive(Debug, Clone, PartialEq, Eq)]
   pub struct Email(String);
   
   impl Email {
       pub fn new(address: &str) -> Result<Self, EmailError> {
           // 验证邮箱格式
           if !is_valid_email(address) {
               return Err(EmailError::InvalidFormat);
           }
           Ok(Email(address.to_string()))
       }
       
       pub fn value(&self) -> &str {
           &self.0
       }
   }
   ```

3. **聚合(Aggregate)**：由一组相关对象组成的集合，通过聚合根(Aggregate Root)访问和修改。

   ```rust
   pub struct Order {
       id: OrderId,
       customer_id: CustomerId,
       items: Vec<OrderItem>,
       status: OrderStatus,
       // 其他属性
   }
   ```

4. **领域服务(Domain Service)**：表示无法自然归属于某个实体或值对象的领域操作。

   ```rust
   pub struct PaymentService {
       // 依赖
   }
   
   impl PaymentService {
       pub fn process_payment(&self, order: &Order, payment_method: &PaymentMethod) -> Result<PaymentReceipt, PaymentError> {
           // 支付处理逻辑
       }
   }
   ```

5. **领域事件(Domain Event)**：记录领域中发生的重要事件，便于系统响应和状态跟踪。

   ```rust
   #[derive(Clone, Debug)]
   pub struct OrderPlaced {
       pub order_id: OrderId,
       pub customer_id: CustomerId,
       pub timestamp: DateTime<Utc>,
       pub items: Vec<OrderItemSummary>,
   }
   ```

6. **限界上下文(Bounded Context)**：一个概念模型的边界，在此边界内所有术语和概念保持一致。

### Rust与DDD的亲和性

Rust语言特性与DDD核心概念有着天然的亲和性：

1. **精确的类型边界**：Rust的类型系统能清晰定义实体和值对象的边界。
2. **不变性支持**：通过所有权系统和不可变引用，可以有效实现值对象的不变性。
3. **聚合封装**：模块系统提供了限制访问路径的能力，支持聚合的封装原则。
4. **领域行为表达**：强大的方法实现和trait系统适合表达领域行为和规则。
5. **编译时验证**：编译器可以捕获许多领域规则违反，提前发现问题。

Rust独特的挑战在于所有权系统对对象关系表达的限制，这需要特殊的设计模式来解决，我们将在后续章节中详细讨论。

## 3. 从概念到代码：Rust类型系统映射

### 实体与值对象的映射

**实体映射策略**:

实体的本质特征是具有标识和生命周期，在Rust中通常表示为包含ID字段的结构体：

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UserId(Uuid);

#[derive(Debug)]
pub struct User {
    id: UserId,
    name: String,
    email: Email,
    created_at: DateTime<Utc>,
    // 其他属性
}

impl User {
    pub fn new(name: String, email: Email) -> Self {
        Self {
            id: UserId(Uuid::new_v4()),
            name,
            email,
            created_at: Utc::now(),
        }
    }
    
    pub fn id(&self) -> &UserId {
        &self.id
    }
    
    pub fn update_email(&mut self, email: Email) {
        self.email = email;
    }
}
```

**值对象映射策略**:

值对象应该是不可变的，其相等性基于所有属性的值而非标识：

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Address {
    street: String,
    city: String,
    state: String,
    postal_code: String,
    country: String,
}

impl Address {
    pub fn new(
        street: String, 
        city: String, 
        state: String, 
        postal_code: String, 
        country: String
    ) -> Result<Self, AddressError> {
        // 验证逻辑
        let address = Self {
            street,
            city,
            state,
            postal_code,
            country,
        };
        
        address.validate()?;
        Ok(address)
    }
    
    fn validate(&self) -> Result<(), AddressError> {
        // 实现验证逻辑
        Ok(())
    }
    
    // 只提供getter，没有setter确保不可变性
    pub fn street(&self) -> &str {
        &self.street
    }
    
    // 其他getter方法
}
```

**ID类型的Newtype模式**:

使用Newtype模式为ID创建强类型，避免不同实体ID混淆：

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OrderId(Uuid);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProductId(Uuid);

// 即使OrderId和ProductId内部都是Uuid，它们是不同的类型
// 编译器会防止误用
```

### 聚合与边界的表达

聚合是保持不变性的边界，聚合根控制对其内部实体的访问：

```rust
pub struct Order {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    shipping_address: Address,
    status: OrderStatus,
    total_amount: Money,
}

impl Order {
    // 构造函数强制验证规则
    pub fn new(
        customer_id: CustomerId,
        shipping_address: Address,
    ) -> Self {
        Self {
            id: OrderId(Uuid::new_v4()),
            customer_id,
            items: Vec::new(),
            shipping_address,
            status: OrderStatus::Draft,
            total_amount: Money::zero(Currency::USD),
        }
    }
    
    // 只能通过聚合根方法修改内部实体
    pub fn add_item(&mut self, product_id: ProductId, quantity: u32, unit_price: Money) -> Result<(), OrderError> {
        if self.status != OrderStatus::Draft {
            return Err(OrderError::CannotModifyNonDraftOrder);
        }
        
        // 创建新的OrderItem
        let item = OrderItem::new(product_id, quantity, unit_price);
        
        // 更新订单
        self.items.push(item);
        self.recalculate_total();
        
        Ok(())
    }
    
    // 内部方法重新计算总金额
    fn recalculate_total(&mut self) {
        self.total_amount = self.items.iter()
            .map(|item| item.subtotal())
            .fold(Money::zero(Currency::USD), |acc, subtotal| acc.add(&subtotal));
    }
    
    // 更多业务方法...
}

// OrderItem作为聚合内的实体
struct OrderItem {
    product_id: ProductId,
    quantity: u32,
    unit_price: Money,
}

impl OrderItem {
    fn new(product_id: ProductId, quantity: u32, unit_price: Money) -> Self {
        Self {
            product_id,
            quantity,
            unit_price,
        }
    }
    
    fn subtotal(&self) -> Money {
        self.unit_price.multiply(self.quantity as f64)
    }
}
```

注意OrderItem没有公共可见性，只能通过Order访问，这强化了聚合边界。

### 关系映射的策略

在Rust中表达不同类型的关系需要采用不同策略：

**1. 组合关系（强所有权）**:

当一个对象包含另一个对象，并控制其生命周期：

```rust
pub struct ShoppingCart {
    id: CartId,
    customer_id: CustomerId,
    items: Vec<CartItem>, // 直接拥有CartItem
    created_at: DateTime<Utc>,
}
```

**2. 引用关系（借用）**:

当需要暂时访问但不拥有对象：

```rust
pub fn calculate_discount(customer: &Customer, order: &Order) -> Money {
    // 使用不可变引用访问但不拥有Customer和Order
}
```

**3. 标识引用（ID关系）**:

跨聚合边界的关系通常使用ID引用：

```rust
pub struct Order {
    id: OrderId,
    customer_id: CustomerId, // 引用Customer，但只存储ID
    // ...
}
```

**4. 复杂关系（智能指针）**:

对于需要共享所有权或有循环引用的情况：

```rust
use std::rc::Rc;
use std::cell::RefCell;

// 在单线程上下文中共享所有权
pub struct Document {
    id: DocumentId,
    sections: Vec<Rc<Section>>, // 多个文档可能共享相同的Section
}

// 对于多线程环境
use std::sync::{Arc, Mutex};

pub struct SharedResource {
    data: Arc<Mutex<ResourceData>>, // 线程安全的共享可变状态
}
```

### 领域规则与不变量实现

Rust提供多种方式确保领域规则和不变量：

**1. 通过构造函数验证**:

```rust
impl Email {
    pub fn new(address: &str) -> Result<Self, EmailError> {
        if !is_valid_email(address) {
            return Err(EmailError::InvalidFormat);
        }
        Ok(Email(address.to_string()))
    }
}
```

**2. 方法前置条件检查**:

```rust
impl Order {
    pub fn submit(&mut self) -> Result<(), OrderError> {
        // 验证前置条件
        if self.items.is_empty() {
            return Err(OrderError::EmptyOrder);
        }
        
        if self.status != OrderStatus::Draft {
            return Err(OrderError::InvalidStatusTransition);
        }
        
        // 执行状态转换
        self.status = OrderStatus::Submitted;
        Ok(())
    }
}
```

**3. 类型系统强制不变量**:

```rust
// 非负整数
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NonNegativeInteger(u32); // 底层类型保证非负

// 正数金额
#[derive(Debug, Clone, PartialEq)]
pub struct PositiveAmount {
    amount: f64,
    currency: Currency,
}

impl PositiveAmount {
    pub fn new(amount: f64, currency: Currency) -> Result<Self, AmountError> {
        if amount <= 0.0 {
            return Err(AmountError::NonPositiveAmount);
        }
        Ok(Self { amount, currency })
    }
}
```

**4. 私有字段和受控访问**:

```rust
pub struct Inventory {
    product_id: ProductId,
    quantity: u32,
    reserved: u32,
    
    // 私有字段确保只能通过方法修改数量
}

impl Inventory {
    pub fn available_quantity(&self) -> u32 {
        self.quantity.saturating_sub(self.reserved)
    }
    
    pub fn reserve(&mut self, amount: u32) -> Result<(), InventoryError> {
        if amount > self.available_quantity() {
            return Err(InventoryError::InsufficientStock);
        }
        self.reserved += amount;
        Ok(())
    }
    
    pub fn release_reservation(&mut self, amount: u32) -> Result<(), InventoryError> {
        if amount > self.reserved {
            return Err(InventoryError::InvalidReleaseAmount);
        }
        self.reserved -= amount;
        Ok(())
    }
}
```

### Rust类型映射的优劣分析

**优势**:

1. **编译时验证**：大量错误在编译时捕获，减少运行时失败。
2. **类型安全**：避免类型混淆，如误用不同实体的ID。
3. **明确所有权**：清晰表达对象生命周期和关系责任。
4. **不可变性支持**：轻松实现值对象不可变性要求。
5. **私有性控制**：可以精确控制对字段的访问，确保封装。

**局限性**:

1. **图状结构困难**：所有权系统使复杂关系图（如双向关系）实现复杂。
2. **运行时验证仍需代码**：类型系统无法表达所有业务规则，仍需额外验证逻辑。
3. **Trait对象限制**：使用Trait对象需要处理'static和Send/Sync约束，增加复杂度。
4. **生命周期标注**：复杂对象图可能需要详细的生命周期标注。
5. **序列化复杂性**：在领域模型和持久化/网络传输之间需要额外映射层。

**最佳实践**:

1. 使用Newtype模式创建领域特定类型。
2. 保持聚合边界小而内聚，避免复杂的对象图。
3. 跨聚合使用ID引用而非直接对象引用。
4. 私有化字段，通过方法控制访问。
5. 构造函数强制验证不变量，返回Result表示可能的失败。

## 4. 动态行为建模：从状态到算法

### 状态机模式实现

许多业务实体都遵循明确的生命周期和状态转换规则，这可以通过状态机模式优雅表达：

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum OrderStatus {
    Draft,
    Submitted,
    Confirmed,
    Shipped,
    Delivered,
    Cancelled,
}

pub enum OrderError {
    EmptyOrder,
    InvalidStatusTransition(OrderStatus, OrderStatus),
    PaymentRequired,
    AlreadyShipped,
    // 其他错误...
}

impl Order {
    pub fn submit(&mut self) -> Result<OrderSubmitted, OrderError> {
        self.ensure_can_transition_to(OrderStatus::Submitted)?;
        
        // 验证业务规则
        if self.items.is_empty() {
            return Err(OrderError::EmptyOrder);
        }
        
        // 执行状态转换
        let previous_status = self.status;
        self.status = OrderStatus::Submitted;
        
        // 生成领域事件
        Ok(OrderSubmitted {
            order_id: self.id.clone(),
            customer_id: self.customer_id.clone(),
            timestamp: Utc::now(),
            previous_status,
        })
    }
    
    pub fn confirm(&mut self) -> Result<OrderConfirmed, OrderError> {
        self.ensure_can_transition_to(OrderStatus::Confirmed)?;
        
        // 可能的其他业务规则检查
        
        // 执行状态转换
        let previous_status = self.status;
        self.status = OrderStatus::Confirmed;
        
        // 生成领域事件
        Ok(OrderConfirmed {
            order_id: self.id.clone(),
            timestamp: Utc::now(),
            previous_status,
        })
    }
    
    // 其他状态转换方法...
    
    // 辅助方法验证状态转换是否合法
    fn ensure_can_transition_to(&self, target_status: OrderStatus) -> Result<(), OrderError> {
        use OrderStatus::*;
        
        match (&self.status, &target_status) {
            // 合法转换
            (Draft, Submitted) => Ok(()),
            (Draft, Cancelled) => Ok(()),
            (Submitted, Confirmed) => Ok(()),
            (Submitted, Cancelled) => Ok(()),
            (Confirmed, Shipped) => Ok(()),
            (Shipped, Delivered) => Ok(()),
            // 允许相同状态（幂等操作）
            (s1, s2) if s1 == s2 => Ok(()),
            // 其他组合都是非法转换
            (current, target) => Err(OrderError::InvalidStatusTransition(
                current.clone(), 
                target.clone()
            )),
        }
    }
}
```

**类型状态模式**:

更高级的方法是使用类型状态(Typestate)模式，通过类型系统在编译时强制状态转换规则：

```rust
// 定义状态类型
pub struct DraftOrder {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    // 共有字段
}

pub struct SubmittedOrder {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    submitted_at: DateTime<Utc>,
    // 共有字段
}

pub struct ConfirmedOrder {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    submitted_at: DateTime<Utc>,
    confirmed_at: DateTime<Utc>,
    // 共有字段
}

// 状态转换方法
impl DraftOrder {
    pub fn new(customer_id: CustomerId) -> Self {
        Self {
            id: OrderId(Uuid::new_v4()),
            customer_id,
            items: Vec::new(),
        }
    }
    
    pub fn add_item(&mut self, product_id: ProductId, quantity: u32, unit_price: Money) {
        // 只有Draft状态可以添加商品
        let item = OrderItem::new(product_id, quantity, unit_price);
        self.items.push(item);
    }
    
    pub fn submit(self) -> Result<SubmittedOrder, OrderError> {
        if self.items.is_empty() {
            return Err(OrderError::EmptyOrder);
        }
        
        Ok(SubmittedOrder {
            id: self.id,
            customer_id: self.customer_id,
            items: self.items,
            submitted_at: Utc::now(),
        })
    }
}

impl SubmittedOrder {
    pub fn confirm(self) -> ConfirmedOrder {
        ConfirmedOrder {
            id: self.id,
            customer_id: self.customer_id,
            items: self.items,
            submitted_at: self.submitted_at,
            confirmed_at: Utc::now(),
        }
    }
    
    pub fn cancel(self) -> CancelledOrder {
        // 实现取消逻辑
    }
}
```

类型状态模式使非法状态在编译时就无法表示，但代价是代码冗余增加。

### 业务过程与领域服务

某些业务逻辑不适合放在单个实体中，这时可以使用领域服务：

```rust
pub struct OrderProcessingService {
    inventory_repository: Box<dyn InventoryRepository>,
    payment_gateway: Box<dyn PaymentGateway>,
}

impl OrderProcessingService {
    pub fn new(
        inventory_repository: Box<dyn InventoryRepository>,
        payment_gateway: Box<dyn PaymentGateway>,
    ) -> Self {
        Self {
            inventory_repository,
            payment_gateway,
        }
    }
    
    pub fn process_order(&self, order: &mut Order, payment_method: PaymentMethod) 
        -> Result<(), OrderProcessingError> {
        
        // 1. 检查库存
        self.check_inventory(order)?;
        
        // 2. 处理支付
        let payment = self.process_payment(order, payment_method)?;
        
        // 3. 更新订单状态
        order.confirm_with_payment(payment)?;
        
        Ok(())
    }
    
    fn check_inventory(&self, order: &Order) -> Result<(), OrderProcessingError> {
        for item in &order.items {
            let inventory = self.inventory_repository.find_by_product_id(&item.product_id)?
                .ok_or(OrderProcessingError::ProductNotFound(item.product_id.clone()))?;
                
            if inventory.available_quantity() < item.quantity {
                return Err(OrderProcessingError::InsufficientStock(
                    item.product_id.clone(),
                    inventory.available_quantity(),
                    item.quantity
                ));
            }
        }
        
        Ok(())
    }
    
    fn process_payment(&self, order: &Order, payment_method: PaymentMethod) 
        -> Result<Payment, OrderProcessingError> {
        
        let payment_result = self.payment_gateway.process(
            order.id(),
            order.total_amount(),
            payment_method
        )?;
        
        Ok(Payment {
            id: PaymentId(Uuid::new_v4()),
            order_id: order.id().clone(),
            amount: order.total_amount(),
            status: PaymentStatus::from(payment_result.status),
            timestamp: Utc::now(),
            transaction_reference: payment_result.transaction_id,
        })
    }
}
```

领域服务应该：

- 专注于特定的业务操作
- 不持有状态（无成员变量，仅依赖）
- 描述多个聚合之间的协作

### 领域事件与事件处理

领域事件代表系统中发生的重要变化，作为聚合操作的返回值可以实现松耦合的事件通知：

```rust
#[derive(Clone, Debug)]
pub struct OrderSubmitted {
    pub order_id: OrderId,
    pub customer_id: CustomerId,
    pub timestamp: DateTime<Utc>,
    pub previous_status: OrderStatus,
}

#[derive(Clone, Debug)]
pub struct OrderConfirmed {
    pub order_id: OrderId,
    pub timestamp: DateTime<Utc>,
    pub previous_status: OrderStatus,
}

// 事件处理示例
pub struct OrderEventHandler {
    notification_service: Box<dyn NotificationService>,
    inventory_service: Box<dyn InventoryService>,
}

impl OrderEventHandler {
    pub fn handle_order_submitted(&self, event: OrderSubmitted) -> Result<(), NotificationError> {
        // 发送确认邮件
        self.notification_service.send_order_confirmation(
            event.customer_id,
            event.order_id,
            event.timestamp,
        )
    }
    
    pub fn handle_order_confirmed(&self, event: OrderConfirmed) -> Result<(), InventoryError> {
        // 为订单预留库存
        self.inventory_service.reserve_inventory(event.order_id)
    }
}
```

在完整的系统中，事件处理通常与消息队列或事件总线集成，实现跨服务通信。

### 异步编程模型与领域逻辑

Rust的异步编程会影响领域逻辑的表达，关键是要控制复杂性：

```rust
// 异步仓储接口
#[async_trait]
pub trait OrderRepository {
    async fn save(&self, order: &Order) -> Result<(), RepositoryError>;
    async fn find_by_id(&self, id: &OrderId) -> Result<Option<Order>, RepositoryError>;
    async fn find_by_customer(&self, customer_id: &CustomerId) -> Result<Vec<Order>, RepositoryError>;
}

// 异步领域服务
pub struct AsyncOrderService {
    order_repository: Arc<dyn OrderRepository + Send + Sync>,
    inventory_repository: Arc<dyn InventoryRepository + Send + Sync>,
    payment_gateway: Arc<dyn PaymentGateway + Send + Sync>,
}

impl AsyncOrderService {
    pub async fn process_order(
        &self, 
        order_id: OrderId, 
        payment_method: PaymentMethod
    ) -> Result<(), OrderProcessingError> {
        // 1. 获取订单
        let mut order = self.order_repository.find_by_id(&order_id).await?
            .ok_or(OrderProcessingError::OrderNotFound(order_id.clone()))?;
            
        // 2. 检查库存
        self.check_inventory(&order).await?;
        
        // 3. 处理支付
        let payment = self.process_payment(&order, payment_method).await?;
        
        // 4. 更新订单状态
        order.confirm_with_payment(payment)?;
        
        // 5. 保存订单
        self.order_repository.save(&order).await?;
        
        Ok(())
    }
    
    async fn check_inventory(&self, order: &Order) -> Result<(), OrderProcessingError> {
        // 异步版本的库存检查
    }
    
    async fn process_payment(&self, order: &Order, payment_method: PaymentMethod) 
        -> Result<Payment, OrderProcessingError> {
        // 异步版本的支付处理
    }
}
```

**异步编程的领域模型考量**:

1. 保持领域模型本身与异步性分离，核心领域逻辑应该是同步的
2. 在应用服务或基础设施层处理异步操作
3. 仔细考虑`Send + Sync`约束对领域模型的影响
4. 使用`#[async_trait]`减轻异步特性带来的样板代码

### 行为验证与形式化方法

对复杂业务行为，可以考虑形式化方法辅助验证：

**属性测试**:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    
    proptest! {
        #[test]
        fn adding_item_increases_total_amount(
            product_id in any::<u64>().prop_map(|id| ProductId(id.into())),
            quantity in 1..100u32,
            unit_price in 1.0..1000.0f64
        ) {
            // 创建测试订单
            let mut order = Order::new(CustomerId(1.into()), 
                                       Address::new_dummy("Test Address"));
            let initial_total = order.total_amount().value();
            
            // 添加商品
            let price = Money::new(unit_price, Currency::USD).unwrap();
            order.add_item(product_id, quantity, price).unwrap();
            
            // 验证总额增加了
            let new_total = order.total_amount().value();
            prop_assert!(new_total > initial_total);
            
            // 验证增加量等于商品小计
            let expected_increase = unit_price * quantity as f64;
            prop_assert_eq!((new_total - initial_total), expected_increase, 
                           "差异小于0.001", |a, b| (a - b).abs() < 0.001);
        }
        
        #[test]
        fn order_status_transitions_are_valid(
            initial_status in prop_oneof![
                Just(OrderStatus::Draft),
                Just(OrderStatus::Submitted),
                Just(OrderStatus::Confirmed),
                Just(OrderStatus::Shipped),
                Just(OrderStatus::Delivered),
                Just(OrderStatus::Cancelled)
            ],
            target_status in prop_oneof![
                Just(OrderStatus::Draft),
                Just(OrderStatus::Submitted),
                Just(OrderStatus::Confirmed),
                Just(OrderStatus::Shipped),
                Just(OrderStatus::Delivered),
                Just(OrderStatus::Cancelled)
            ]
        ) {
            let mut order = Order::new(CustomerId(1.into()), 
                                      Address::new_dummy("Test Address"));
            
            // 设置初始状态（通过反射或测试辅助方法）
            order.test_set_status(initial_status);
            
            // 尝试状态转换
            let result = order.test_transition_to(target_status);
            
            // 校验合法的转换应成功，非法的应失败
            match (initial_status, target_status) {
                (OrderStatus::Draft, OrderStatus::Submitted) => prop_assert!(result.is_ok()),
                (OrderStatus::Draft, OrderStatus::Cancelled) => prop_assert!(result.is_ok()),
                (OrderStatus::Submitted, OrderStatus::Confirmed) => prop_assert!(result.is_ok()),
                (OrderStatus::Submitted, OrderStatus::Cancelled) => prop_assert!(result.is_ok()),
                (OrderStatus::Confirmed, OrderStatus::Shipped) => prop_assert!(result.is_ok()),
                (OrderStatus::Shipped, OrderStatus::Delivered) => prop_assert!(result.is_ok()),
                (a, b) if a == b => prop_assert!(result.is_ok()), // 相同状态允许
                _ => prop_assert!(result.is_err()), // 其他都是非法转换
            }
        }
    }
}
```

**状态不变量验证**:

```rust
impl Order {
    // 确保每次修改后验证不变量
    fn ensure_invariants(&self) -> Result<(), OrderError> {
        // 1. 订单总额必须等于所有商品小计之和
        let calculated_total = self.items.iter()
            .map(|item| item.subtotal().value())
            .sum::<f64>();
            
        if (self.total_amount.value() - calculated_total).abs() > 0.001 {
            return Err(OrderError::InconsistentTotalAmount);
        }
        
        // 2. 已取消订单不能有任何进一步修改
        if self.status == OrderStatus::Cancelled && self.modified_after_cancel {
            return Err(OrderError::ModifiedAfterCancellation);
        }
        
        // 可以添加更多不变量检查
        
        Ok(())
    }
}

// 在测试中可以更全面地验证
#[test]
fn order_maintains_invariants_after_operations() {
    let mut order = Order::new(customer_id, address);
    
    // 添加商品
    order.add_item(product_id, 2, price).unwrap();
    assert!(order.ensure_invariants().is_ok());
    
    // 修改数量
    order.update_item_quantity(0, 5).unwrap();
    assert!(order.ensure_invariants().is_ok());
    
    // 移除商品
    order.remove_item(0).unwrap();
    assert!(order.ensure_invariants().is_ok());
}
```

**模型检查**:

对于更复杂的行为验证，可以考虑使用专门的模型检查工具或TLA+等形式化规约语言建立系统模型，虽然这超出了Rust自身的范围，但对验证复杂业务规则非常有价值。

## 5. 分层架构：关注点分离的工程实践

### 整洁架构与端口适配器模式

整洁架构（Clean Architecture）和端口适配器模式（Ports and Adapters/Hexagonal Architecture）提供了组织代码的强大框架，将业务核心与技术细节分离。核心思想是：

1. **依赖方向**: 所有依赖都应指向领域核心，而不是从领域核心向外部依赖
2. **关注点分离**: 不同层负责不同关注点，相互之间通过定义良好的接口通信
3. **可测试性**: 核心业务逻辑可以在不涉及UI、数据库等外部依赖的情况下测试

在Rust中实现这种架构的基础是使用模块系统和特质（Trait）：

```text
src/
  ├── domain/         # 领域层：核心业务逻辑和规则
  │   ├── model/      # 领域模型实体、值对象和聚合
  │   ├── service/    # 领域服务
  │   ├── event/      # 领域事件
  │   └── repository/ # 仓储接口（端口）
  │
  ├── application/    # 应用层：用例和业务流程协调
  │   ├── service/    # 应用服务
  │   ├── dto/        # 数据传输对象
  │   ├── command/    # 命令对象（如果使用CQRS）
  │   └── query/      # 查询对象（如果使用CQRS）
  │
  ├── infrastructure/ # 基础设施层：技术细节实现
  │   ├── repository/ # 仓储实现（适配器）
  │   ├── persistence/# 持久化相关代码
  │   ├── messaging/  # 消息传递实现
  │   └── api/        # 外部API客户端
  │
  └── interface/      # 接口层：用户接口实现
      ├── rest/       # REST API控制器
      ├── cli/        # 命令行接口
      └── grpc/       # gRPC服务实现
```

### 领域层：业务核心的纯粹表达

领域层是整个系统的核心，包含业务概念和规则的纯粹表达，应保持独立于技术细节：

```rust
// 领域模型示例 - src/domain/model/order.rs
pub struct Order {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    status: OrderStatus,
    total_amount: Money,
    // 其他核心属性
}

impl Order {
    // 核心业务规则和行为...
}

// 领域服务示例 - src/domain/service/pricing_service.rs
pub struct PricingService {
    discount_policy: Box<dyn DiscountPolicy>,
}

impl PricingService {
    pub fn new(discount_policy: Box<dyn DiscountPolicy>) -> Self {
        Self { discount_policy }
    }
    
    pub fn calculate_price(&self, order: &Order) -> Money {
        // 计算价格，应用折扣策略等
    }
}

// 仓储接口（端口）- src/domain/repository/order_repository.rs
pub trait OrderRepository {
    fn save(&self, order: &Order) -> Result<(), RepositoryError>;
    fn find_by_id(&self, id: &OrderId) -> Result<Option<Order>, RepositoryError>;
    // 其他查询/修改方法
}
```

领域层的关键特点：

1. **不依赖外部库**: 除了Rust标准库和极少数通用工具（如uuid, chrono），不引入外部依赖
2. **纯粹的业务逻辑**: 所有代码都应直接表达业务概念和规则
3. **抽象接口（端口）**: 定义领域需要的外部功能，但不依赖具体实现
4. **丰富的领域语言**: 代码应该读起来像业务语言，表达力强
5. **所有依赖方向向内**: 其他层依赖领域层，而不是反过来

### 应用层：用例协调与业务流程

应用层充当领域层与外部世界之间的桥梁，协调整体业务流程：

```rust
// 应用服务 - src/application/service/order_service.rs
pub struct OrderService {
    order_repository: Arc<dyn OrderRepository>,
    customer_repository: Arc<dyn CustomerRepository>,
    pricing_service: PricingService,
    notification_service: Arc<dyn NotificationService>,
}

impl OrderService {
    pub fn new(
        order_repository: Arc<dyn OrderRepository>,
        customer_repository: Arc<dyn CustomerRepository>,
        pricing_service: PricingService,
        notification_service: Arc<dyn NotificationService>,
    ) -> Self {
        Self {
            order_repository,
            customer_repository,
            pricing_service,
            notification_service,
        }
    }
    
    pub fn create_order(&self, command: CreateOrderCommand) -> Result<OrderDto, ApplicationError> {
        // 1. 获取客户信息
        let customer = self.customer_repository.find_by_id(&command.customer_id)?
            .ok_or(ApplicationError::CustomerNotFound(command.customer_id.clone()))?;
            
        // 2. 创建订单领域对象
        let mut order = Order::new(command.customer_id, command.shipping_address);
        
        // 3. 添加商品
        for item in command.items {
            order.add_item(item.product_id, item.quantity, item.unit_price)?;
        }
        
        // 4. 应用定价规则
        let total = self.pricing_service.calculate_price(&order);
        order.update_total(total)?;
        
        // 5. 保存订单
        self.order_repository.save(&order)?;
        
        // 6. 发送通知
        self.notification_service.send_order_created(
            &customer.email, 
            &order.id, 
            order.total_amount()
        )?;
        
        // 7. 返回DTO
        Ok(OrderDto::from(order))
    }
    
    // 其他用例...
}

// 数据传输对象 - src/application/dto/order_dto.rs
#[derive(Debug, Clone, Serialize)]
pub struct OrderDto {
    pub id: String,
    pub customer_id: String,
    pub status: String,
    pub items: Vec<OrderItemDto>,
    pub total_amount: f64,
    pub currency: String,
    // 其他属性
}

impl From<Order> for OrderDto {
    fn from(order: Order) -> Self {
        Self {
            id: order.id().to_string(),
            customer_id: order.customer_id().to_string(),
            status: format!("{:?}", order.status()),
            items: order.items().iter().map(OrderItemDto::from).collect(),
            total_amount: order.total_amount().value(),
            currency: format!("{:?}", order.total_amount().currency()),
        }
    }
}

// 命令对象 - src/application/command/create_order_command.rs
#[derive(Debug, Clone, Deserialize)]
pub struct CreateOrderCommand {
    pub customer_id: CustomerId,
    pub shipping_address: Address,
    pub items: Vec<OrderItemCommand>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct OrderItemCommand {
    pub product_id: ProductId,
    pub quantity: u32,
    pub unit_price: Money,
}
```

应用层的关键特点：

1. **协调业务流程**: 编排多个领域对象和服务来完成用例
2. **转换数据**: 在系统边界和领域模型之间转换数据（DTO）
3. **处理事务边界**: 确保业务操作的原子性
4. **依赖注入**: 通过构造函数接收领域层定义的端口（抽象接口）
5. **不包含业务规则**: 业务规则属于领域层，应用层只负责协调

### 基础设施层：技术关注点封装

基础设施层实现领域层定义的端口（接口），提供与外部系统的连接，封装技术细节：

```rust
// 仓储实现（适配器）- src/infrastructure/repository/postgres_order_repository.rs
use sqlx::PgPool;

pub struct PostgresOrderRepository {
    pool: PgPool,
}

impl PostgresOrderRepository {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
}

impl OrderRepository for PostgresOrderRepository {
    fn save(&self, order: &Order) -> Result<(), RepositoryError> {
        // 使用sqlx与PostgreSQL交互，实现保存逻辑
        todo!()
    }
    
    fn find_by_id(&self, id: &OrderId) -> Result<Option<Order>, RepositoryError> {
        // 实现查询逻辑
        todo!()
    }
    
    // 实现其他方法...
}

// 消息服务实现 - src/infrastructure/messaging/kafka_event_publisher.rs
pub struct KafkaEventPublisher {
    producer: KafkaProducer,
    // 配置和其他依赖
}

impl KafkaEventPublisher {
    pub fn new(bootstrap_servers: &str) -> Result<Self, KafkaError> {
        // 配置Kafka生产者
        todo!()
    }
}

impl EventPublisher for KafkaEventPublisher {
    fn publish<E: Event>(&self, event: &E) -> Result<(), PublishError> {
        // 序列化事件并发送到Kafka
        todo!()
    }
}

// 通知服务实现 - src/infrastructure/notification/email_notification_service.rs
pub struct EmailNotificationService {
    email_client: MailClient,
    template_engine: TemplateEngine,
}

impl NotificationService for EmailNotificationService {
    fn send_order_created(&self, email: &str, order_id: &OrderId, amount: Money) -> Result<(), NotificationError> {
        // 生成邮件内容并发送
        todo!()
    }
}
```

基础设施层的关键特点：

1. **实现抽象接口**: 提供领域层定义的端口的具体实现
2. **封装技术细节**: 隐藏外部系统交互的复杂性
3. **处理持久化**: 实现数据库访问、ORM映射等
4. **集成外部服务**: 连接第三方API、消息队列等
5. **管理技术资源**: 连接池、客户端等的生命周期管理

## 6. Rust技术栈选型与应用

### 领域层技术选择

领域层应保持最小化的技术依赖，以确保核心业务逻辑的纯粹性：

**适合领域层的库**:

| 库名 | 用途 | 说明 |
|------|------|------|
| `uuid` | 唯一标识符 | 用于实体ID，较为通用，影响较小 |
| `chrono` | 日期和时间处理 | 用于时间戳等，API稳定，领域概念相关 |
| `rust_decimal` | 精确小数计算 | 适合财务计算，避免浮点误差 |
| `thiserror` | 错误处理 | 简化领域错误类型定义 |
| `strum` | 枚举工具 | 增强枚举类型的使用体验 |

**代码示例**:

```rust
use uuid::Uuid;
use chrono::{DateTime, Utc};
use rust_decimal::Decimal;
use thiserror::Error;
use strum_macros::{Display, EnumString};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OrderId(Uuid);

impl OrderId {
    pub fn new() -> Self {
        Self(Uuid::new_v4())
    }
    
    pub fn from_string(s: &str) -> Result<Self, uuid::Error> {
        Ok(Self(Uuid::parse_str(s)?))
    }
}

#[derive(Debug, Display, EnumString, Clone, PartialEq)]
pub enum PaymentStatus {
    Pending,
    Authorized,
    Captured,
    Refunded,
    Failed,
}

#[derive(Error, Debug)]
pub enum OrderError {
    #[error("Cannot add items to an order with status {0}")]
    InvalidOrderStateForAddingItems(OrderStatus),
    
    #[error("Insufficient stock for product {0}: requested {1}, available {2}")]
    InsufficientStock(ProductId, u32, u32),
    
    #[error("Invalid payment amount: expected {expected}, got {actual}")]
    InvalidPaymentAmount { expected: Decimal, actual: Decimal },
    
    // 其他错误...
}
```

### 应用层技术选择

应用层需要处理更多的技术关注点，但仍应适度克制：

**适合应用层的库**:

| 库名 | 用途 | 说明 |
|------|------|------|
| `serde` + `serde_json` | 序列化/反序列化 | DTO转换，命令/查询对象处理 |
| `async-trait` | 异步trait支持 | 允许在trait中使用async函数 |
| `validator` | 数据验证 | 验证输入命令和DTO |
| `anyhow` | 错误处理 | 应用层错误包装 |
| `futures` | 异步编程原语 | 并发操作组合 |

**代码示例**:

```rust
use serde::{Serialize, Deserialize};
use validator::{Validate, ValidationError};
use async_trait::async_trait;
use anyhow::{Context, Result};

#[derive(Debug, Deserialize, Validate)]
pub struct CreateUserCommand {
    #[validate(length(min = 3, max = 50))]
    pub username: String,
    
    #[validate(email)]
    pub email: String,
    
    #[validate(length(min = 8))]
    pub password: String,
}

#[derive(Debug, Serialize)]
pub struct UserDto {
    pub id: String,
    pub username: String,
    pub email: String,
    pub created_at: String,
}

#[async_trait]
pub trait UserService {
    async fn create_user(&self, command: CreateUserCommand) -> Result<UserDto>;
    async fn get_user(&self, id: &str) -> Result<Option<UserDto>>;
    async fn update_email(&self, id: &str, new_email: &str) -> Result<()>;
}

pub struct UserServiceImpl {
    user_repository: Arc<dyn UserRepository + Send + Sync>,
    password_hasher: Arc<dyn PasswordHasher + Send + Sync>,
    event_publisher: Arc<dyn EventPublisher + Send + Sync>,
}

#[async_trait]
impl UserService for UserServiceImpl {
    async fn create_user(&self, command: CreateUserCommand) -> Result<UserDto> {
        // 验证命令
        command.validate()
            .context("Invalid user data")?;
            
        // 检查用户名是否已存在
        if self.user_repository.find_by_username(&command.username).await?.is_some() {
            anyhow::bail!("Username already taken");
        }
        
        // 创建用户领域对象
        let hashed_password = self.password_hasher.hash_password(&command.password)
            .context("Failed to hash password")?;
            
        let user = User::new(
            UserId::new(),
            command.username,
            Email::new(&command.email)?,
            hashed_password,
        );
        
        // 保存用户
        self.user_repository.save(&user).await
            .context("Failed to save user")?;
            
        // 发布事件
        let event = UserCreatedEvent {
            user_id: user.id().clone(),
            username: user.username().to_string(),
            timestamp: Utc::now(),
        };
        
        self.event_publisher.publish(&event).await
            .context("Failed to publish user created event")?;
            
        // 返回DTO
        Ok(UserDto {
            id: user.id().to_string(),
            username: user.username().to_string(),
            email: user.email().value().to_string(),
            created_at: user.created_at().to_rfc3339(),
        })
    }
    
    // 其他方法实现...
}
```

### 基础设施层技术栈全景

基础设施层涉及各种技术集成，需要根据具体需求选择合适的库：

#### 异步运行时与并发

| 库名 | 优势 | 适用场景 | 成熟度 |
|------|------|---------|--------|
| `tokio` | 全功能、高性能、生态最强 | 需要完整异步功能栈的应用 | 非常成熟 |
| `async-std` | API设计接近标准库、直观 | 希望平滑过渡到异步的应用 | 成熟 |
| `rayon` | 数据并行处理、简单易用 | CPU密集型任务、并行数据处理 | 成熟 |
| `futures` | 异步原语、灵活组合 | 构建自定义异步抽象 | 成熟 |

**最佳实践**:

- 大多数项目选择`tokio`作为异步运行时，生态最完整
- CPU密集型任务考虑使用`rayon`实现数据并行
- 避免混合多个异步运行时，可能导致兼容性问题

#### 数据持久化方案

| 库名 | 优势 | 适用场景 | 成熟度 |
|------|------|---------|--------|
| `sqlx` | 编译时检查SQL、异步支持 | 需要细粒度SQL控制 | 成熟 |
| `diesel` | 完整ORM、类型安全查询构建 | 关系型数据库、复杂模型 | 非常成熟 |
| `sea-orm` | 异步ORM、完整功能 | 需要异步ORM的应用 | 较成熟 |
| `mongodb` | 官方MongoDB驱动、异步 | MongoDB数据库集成 | 成熟 |
| `redis` | Redis客户端、支持异步 | 缓存、会话存储 | 成熟 |

**最佳实践**:

- 关系型数据库：偏好SQL控制选`sqlx`，偏好ORM选`diesel`或`sea-orm`
- 需要异步数据库访问：选择`sqlx`或`sea-orm`
- 实现`Repository`接口，将数据访问与领域逻辑分离
- 使用模型映射器（mapper）在领域模型和数据库模型间转换

**代码示例**:

```rust
// 使用sqlx的仓储实现
pub struct SqlxOrderRepository {
    pool: PgPool,
}

impl SqlxOrderRepository {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
    
    // 将领域模型映射到数据库记录
    fn to_db_model(&self, order: &Order) -> OrderDbModel {
        OrderDbModel {
            id: order.id().to_string(),
            customer_id: order.customer_id().to_string(),
            status: order.status().to_string(),
            total_amount: order.total_amount().value(),
            currency: order.total_amount().currency().to_string(),
            created_at: order.created_at(),
            updated_at: Utc::now(),
        }
    }
    
    // 将数据库记录映射到领域模型
    fn to_domain_model(&self, db_model: OrderDbModel, items: Vec<OrderItemDbModel>) -> Result<Order, RepositoryError> {
        // 实现映射逻辑
        todo!()
    }
}

#[async_trait]
impl OrderRepository for SqlxOrderRepository {
    async fn save(&self, order: &Order) -> Result<(), RepositoryError> {
        let db_model = self.to_db_model(order);
        
        // 开始事务
        let mut tx = self.pool.begin().await
            .map_err(|e| RepositoryError::DatabaseError(e.to_string()))?;
            
        // 保存订单主记录
        sqlx::query(
            "INSERT INTO orders (id, customer_id, status, total_amount, currency, created_at, updated_at)
             VALUES ($1, $2, $3, $4, $5, $6, $7)
             ON CONFLICT (id) DO UPDATE SET
                status = $3,
                total_amount = $4,
                currency = $5,
                updated_at = $7"
        )
        .bind(&db_model.id)
        .bind(&db_model.customer_id)
        .bind(&db_model.status)
        .bind(db_model.total_amount)
        .bind(&db_model.currency)
        .bind(db_model.created_at)
        .bind(db_model.updated_at)
        .execute(&mut tx)
        .await
        .map_err(|e| RepositoryError::DatabaseError(e.to_string()))?;
        
        // 保存订单项目
        for item in order.items() {
            let item_model = self.to_item_db_model(item, &order.id());
            
            sqlx::query(
                "INSERT INTO order_items (id, order_id, product_id, quantity, unit_price, currency)
                 VALUES ($1, $2, $3, $4, $5, $6)
                 ON CONFLICT (id) DO UPDATE SET
                    quantity = $4,
                    unit_price = $5,
                    currency = $6"
            )
            .bind(&item_model.id)
            .bind(&item_model.order_id)
            .bind(&item_model.product_id)
            .bind(item_model.quantity)
            .bind(item_model.unit_price)
            .bind(&item_model.currency)
            .execute(&mut tx)
            .await
            .map_err(|e| RepositoryError::DatabaseError(e.to_string()))?;
        }
        
        // 提交事务
        tx.commit().await
            .map_err(|e| RepositoryError::DatabaseError(e.to_string()))?;
            
        Ok(())
    }
    
    async fn find_by_id(&self, id: &OrderId) -> Result<Option<Order>, RepositoryError> {
        // 实现查询逻辑
        todo!()
    }
}
```

#### Web与网络框架

| 库名 | 优势 | 适用场景 | 成熟度 |
|------|------|---------|--------|
| `axum` | 现代设计、低样板代码、类型安全 | 新项目、希望优雅API的应用 | 成熟且活跃 |
| `actix-web` | 高性能、功能丰富、生态成熟 | 需要完整功能集的应用 | 非常成熟 |
| `rocket` | 简洁API、强调开发体验 | 注重简洁与表达力的应用 | 成熟 |
| `warp` | 函数式、组合过滤器 | 偏好函数式风格的应用 | 成熟 |
| `tonic` | gRPC框架、代码生成 | 微服务间通信、性能关键应用 | 成熟 |
| `reqwest` | HTTP客户端、易用 | 调用外部API | 非常成熟 |

**最佳实践**:

- `axum`和`actix-web`是最流行的选择，前者更现代，后者生态更完整
- Web框架应限制在接口层或基础设施的适配器实现中
- 实现依赖注入以连接控制器与应用服务
- 使用中间件处理横切关注点（认证、日志、错误处理）

**代码示例**:

```rust
// 使用axum实现REST API
use axum::{
    routing::{get, post},
    http::StatusCode,
    extract::{Path, State, Json},
    Router,
};
use tower_http::trace::TraceLayer;

// 应用状态包含依赖服务
struct AppState {
    order_service: Arc<dyn OrderService + Send + Sync>,
    // 其他依赖...
}

// 启动HTTP服务器
async fn start_http_server() -> Result<(), anyhow::Error> {
    // 创建依赖
    let pg_pool = PgPoolOptions::new()
        .max_connections(32)
        .connect(&std::env::var("DATABASE_URL")?)
        .await?;
        
    let order_repository = Arc::new(PostgresOrderRepository::new(pg_pool.clone()));
    let customer_repository = Arc::new(PostgresCustomerRepository::new(pg_pool));
    let notification_service = Arc::new(EmailNotificationService::new(
        /* email配置 */
    ));
    
    let pricing_service = PricingService::new(
        Box::new(StandardDiscountPolicy::new())
    );
    
    // 创建应用服务
    let order_service = Arc::new(OrderServiceImpl::new(
        order_repository,
        customer_repository,
        pricing_service,
        notification_service,
    ));
    
    // 创建应用状态
    let state = Arc::new(AppState {
        order_service,
    });
    
    // 构建路由
    let app = Router::new()
        .route("/api/orders", post(create_order))
        .route("/api/orders/:id", get(get_order))
        .route("/api/orders/:id/cancel", post(cancel_order))
        // 添加中间件
        .layer(TraceLayer::new_for_http())
        .with_state(state);
        
    // 启动服务器
    let addr = SocketAddr::from(([127, 0, 0, 1], 3000));
    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await?;
        
    Ok(())
}

// 处理函数
async fn create_order(
    State(state): State<Arc<AppState>>,
    Json(command): Json<CreateOrderCommand>,
) -> Result<(StatusCode, Json<OrderDto>), AppError> {
    // 调用应用服务
    let order = state.order_service.create_order(command).await?;
    Ok((StatusCode::CREATED, Json(order)))
}

async fn get_order(
    State(state): State<Arc<AppState>>,
    Path(id): Path<String>,
) -> Result<Json<OrderDto>, AppError> {
    let order_id = OrderId::from_string(&id)
        .map_err(|_| AppError::InvalidId)?;
        
    let order = state.order_service.get_order(&order_id).await?
        .ok_or(AppError::NotFound)?;
        
    Ok(Json(order))
}

// 错误处理
enum AppError {
    InvalidId,
    NotFound,
    ServiceError(anyhow::Error),
    ValidationError(validator::ValidationErrors),
}

impl From<anyhow::Error> for AppError {
    fn from(err: anyhow::Error) -> Self {
        Self::ServiceError(err)
    }
}

impl IntoResponse for AppError {
    fn into_response(self) -> axum::response::Response {
        let (status, message) = match self {
            Self::InvalidId => (StatusCode::BAD_REQUEST, "Invalid ID format".to_string()),
            Self::NotFound => (StatusCode::NOT_FOUND, "Resource not found".to_string()),
            Self::ValidationError(errors) => (StatusCode::BAD_REQUEST, errors.to_string()),
            Self::ServiceError(err) => (StatusCode::INTERNAL_SERVER_ERROR, err.to_string()),
        };
        
        let json = Json(serde_json::json!({
            "error": message
        }));
        
        (status, json).into_response()
    }
}
```

#### 序列化与通信

| 库名 | 优势 | 适用场景 | 成熟度 |
|------|------|---------|--------|
| `serde` | 通用序列化框架、强大定制 | 几乎所有项目的基础 | 非常成熟 |
| `serde_json` | JSON格式支持 | REST API、配置文件 | 非常成熟 |
| `serde_yaml` | YAML格式支持 | 配置文件、数据导出 | 成熟 |
| `prost` | Protocol Buffers | 高效RPC、schema定义 | 成熟 |
| `bincode` | 二进制序列化 | 内部通信、存储 | 成熟 |
| `messagepack` | 紧凑二进制格式 | 高效网络传输 | 成熟 |

**最佳实践**:

- 几乎所有项目都需要`serde`作为序列化基础
- 使用`#[serde(rename_all = "camelCase")]`统一API响应格式
- 使用`#[serde(skip_serializing_if = "Option::is_none")]`优化输出
- 考虑为领域模型和DTO分别实现序列化，避免暴露内部细节

#### 配置与日志

| 库名 | 优势 | 适用场景 | 成熟度 |
|------|------|---------|--------|
| `config` | 多来源配置、格式转换 | 复杂配置需求 | 成熟 |
| `dotenvy` | 环境变量加载 | 简单配置、本地开发 | 成熟 |
| `tracing` | 结构化日志、span跟踪 | 现代应用、可观测性 | 成熟且活跃 |
| `log` | 简单日志接口 | 基础日志需求 | 非常成熟 |
| `env_logger` | 环境变量配置、简单易用 | 简单应用、开发环境 | 成熟 |
| `tracing-subscriber` | 灵活的日志收集配置 | 与`tracing`配合使用 | 成熟 |
| `slog` | 结构化、高性能日志 | 高性能日志需求 | 成熟 |
| `clap` | 强大的命令行参数解析 | CLI应用、服务配置 | 非常成熟 |

**最佳实践**:

- 使用`config`库集中处理各种配置源
- 采用`tracing`实现结构化日志，便于后续分析
- 配置独立模块封装配置加载和验证逻辑
- 应用启动时进行完整的配置验证

**代码示例**:

```rust
// 配置模块 - src/infrastructure/config/mod.rs
use serde::Deserialize;
use config::{Config, ConfigError, Environment, File};

#[derive(Debug, Deserialize)]
pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
    pub timeout_seconds: u64,
}

#[derive(Debug, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub request_timeout_ms: u64,
}

#[derive(Debug, Deserialize)]
pub struct LoggingConfig {
    pub level: String,
    pub json_format: bool,
}

#[derive(Debug, Deserialize)]
pub struct AppConfig {
    pub database: DatabaseConfig,
    pub server: ServerConfig,
    pub logging: LoggingConfig,
    pub environment: String,
}

impl AppConfig {
    pub fn load() -> Result<Self, ConfigError> {
        let environment = std::env::var("APP_ENV").unwrap_or_else(|_| "development".into());
        
        let config = Config::builder()
            // 1. 默认值
            .set_default("environment", "development")?
            // 2. 基本配置文件
            .add_source(File::with_name("config/default"))
            // 3. 环境特定配置
            .add_source(File::with_name(&format!("config/{}", environment)).required(false))
            // 4. 本地开发覆盖
            .add_source(File::with_name("config/local").required(false))
            // 5. 环境变量 (APP_DATABASE__URL 等)
            .add_source(Environment::with_prefix("APP").separator("__"))
            .build()?;
            
        // 转换为结构体
        config.try_deserialize()
    }
    
    pub fn validate(&self) -> Result<(), String> {
        // 验证配置的有效性
        if self.database.max_connections == 0 {
            return Err("Database max_connections must be greater than 0".to_string());
        }
        
        if self.server.port == 0 {
            return Err("Server port must be greater than 0".to_string());
        }
        
        Ok(())
    }
}

// 日志配置 - src/infrastructure/logging/mod.rs
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter, Registry};
use tracing_bunyan_formatter::{BunyanFormattingLayer, JsonStorageLayer};

pub fn init_logging(config: &LoggingConfig) -> Result<(), String> {
    let env_filter = EnvFilter::try_from_default_env()
        .or_else(|_| EnvFilter::try_new(&config.level))
        .map_err(|e| format!("Failed to create EnvFilter: {}", e))?;
        
    if config.json_format {
        // JSON格式化日志 (适合生产环境)
        let formatting_layer = BunyanFormattingLayer::new(
            "app_name".into(),
            std::io::stdout
        );
        
        Registry::default()
            .with(env_filter)
            .with(JsonStorageLayer)
            .with(formatting_layer)
            .init();
    } else {
        // 终端友好的日志 (适合开发环境)
        let fmt_layer = tracing_subscriber::fmt::layer().pretty();
        
        Registry::default()
            .with(env_filter)
            .with(fmt_layer)
            .init();
    }
    
    Ok(())
}

// 应用启动 - src/main.rs
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 加载配置
    let config = AppConfig::load()?;
    config.validate()?;
    
    // 初始化日志
    init_logging(&config.logging)?;
    
    // 记录启动信息
    tracing::info!(
        environment = %config.environment,
        server.port = %config.server.port,
        "Application starting"
    );
    
    // 后续启动逻辑...
    
    Ok(())
}
```

## 7. 高级架构模式与Rust实现

### CQRS模式

命令查询责任分离（Command Query Responsibility Segregation，CQRS）模式将系统操作分为命令（修改状态）和查询（获取状态）两部分，可以针对它们分别优化：

**模式概述**:

- **命令端**: 处理修改操作，强调正确性和一致性
- **查询端**: 处理读取操作，强调性能和可扩展性
- **数据同步**: 通过事件或其他机制在两端同步数据

**Rust实现**:

```rust
// 命令处理 - 领域模型强调正确性
pub struct CreateProductCommand {
    pub name: String,
    pub description: String,
    pub price: Money,
    pub stock_level: u32,
}

pub struct ProductCommandService {
    product_repository: Arc<dyn ProductRepository>,
    event_publisher: Arc<dyn EventPublisher>,
}

impl ProductCommandService {
    pub async fn create_product(
        &self, 
        command: CreateProductCommand
    ) -> Result<ProductId, DomainError> {
        // 验证业务规则
        if command.price.value() <= Decimal::ZERO {
            return Err(DomainError::InvalidPrice);
        }
        
        // 创建领域实体
        let product_id = ProductId::new();
        let product = Product::new(
            product_id.clone(),
            command.name,
            command.description,
            command.price,
            command.stock_level,
        );
        
        // 持久化
        self.product_repository.save(&product).await?;
        
        // 发布事件
        let event = ProductCreatedEvent {
            product_id: product.id().clone(),
            name: product.name().to_string(),
            price: product.price().clone(),
            timestamp: Utc::now(),
        };
        
        self.event_publisher.publish(&event).await?;
        
        Ok(product_id)
    }
    
    // 其他命令处理方法...
}

// 查询处理 - 针对查询场景优化
#[derive(Debug, Serialize)]
pub struct ProductListItemDto {
    pub id: String,
    pub name: String,
    pub price: f64,
    pub available: bool,
}

#[derive(Debug, Serialize)]
pub struct ProductDetailDto {
    pub id: String,
    pub name: String,
    pub description: String,
    pub price: f64,
    pub currency: String,
    pub stock_level: u32,
    pub available: bool,
    pub created_at: String,
    pub category_name: String,
    pub ratings_average: Option<f64>,
}

pub struct ProductQueryService {
    db_pool: PgPool, // 直接访问数据库
}

impl ProductQueryService {
    pub async fn find_products(
        &self,
        category_id: Option<String>,
        min_price: Option<f64>,
        max_price: Option<f64>,
        available_only: bool,
        page: u32,
        page_size: u32,
    ) -> Result<Vec<ProductListItemDto>, QueryError> {
        // 直接使用SQL优化查询（可能包含连接多个表）
        let mut query = sqlx::QueryBuilder::new(
            "SELECT p.id, p.name, p.price, (p.stock_level > 0) as available
             FROM products p
             LEFT JOIN product_categories pc ON p.id = pc.product_id
             WHERE 1=1"
        );
        
        // 添加条件
        if let Some(category_id) = category_id {
            query.push(" AND pc.category_id = ");
            query.push_bind(category_id);
        }
        
        if let Some(min_price) = min_price {
            query.push(" AND p.price >= ");
            query.push_bind(min_price);
        }
        
        if let Some(max_price) = max_price {
            query.push(" AND p.price <= ");
            query.push_bind(max_price);
        }
        
        if available_only {
            query.push(" AND p.stock_level > 0");
        }
        
        // 添加分页
        query.push(" ORDER BY p.name");
        query.push(" LIMIT ");
        query.push_bind(page_size);
        query.push(" OFFSET ");
        query.push_bind((page - 1) * page_size);
        
        let products = query.build()
            .map(|row: PgRow| {
                ProductListItemDto {
                    id: row.get("id"),
                    name: row.get("name"),
                    price: row.get("price"),
                    available: row.get("available"),
                }
            })
            .fetch_all(&self.db_pool)
            .await
            .map_err(|e| QueryError::DatabaseError(e.to_string()))?;
            
        Ok(products)
    }
    
    pub async fn get_product_details(&self, id: &str) -> Result<Option<ProductDetailDto>, QueryError> {
        // 单个产品详情查询，可能需要关联多个表
        let product = sqlx::query_as!(
            ProductDetailDto,
            r#"
            SELECT 
                p.id, p.name, p.description, p.price, p.currency,
                p.stock_level, (p.stock_level > 0) as "available!",
                p.created_at::text, c.name as category_name,
                (SELECT AVG(rating) FROM product_ratings WHERE product_id = p.id) as "ratings_average?"
            FROM products p
            LEFT JOIN product_categories pc ON p.id = pc.product_id
            LEFT JOIN categories c ON pc.category_id = c.id
            WHERE p.id = $1
            "#,
            id
        )
        .fetch_optional(&self.db_pool)
        .await
        .map_err(|e| QueryError::DatabaseError(e.to_string()))?;
        
        Ok(product)
    }
}
```

**CQRS最佳实践**:

1. 从简单开始，只有在确实需要时再引入CQRS复杂性
2. 考虑命令和查询模型的一致性要求，选择合适的同步策略
3. 查询模型可以针对特定用例高度优化，不必遵循标准化的领域模型
4. 使用事件驱动方法同步两个模型，确保最终一致性
5. 留意查询模型的缓存策略，合理处理数据过期问题

### 事件溯源

事件溯源（Event Sourcing）将系统状态的所有变更存储为事件序列，而不是仅存储当前状态：

**模式概述**:

- **事件存储**: 系统的事实来源是事件流
- **状态重构**: 通过重放事件重构实体的当前状态
- **事件投影**: 创建针对查询优化的视图

**Rust实现**:

```rust
// 领域事件 - src/domain/event/order_events.rs
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum OrderEvent {
    OrderCreated {
        order_id: String,
        customer_id: String,
        timestamp: DateTime<Utc>,
    },
    OrderItemAdded {
        order_id: String,
        product_id: String,
        quantity: u32,
        unit_price: f64,
        timestamp: DateTime<Utc>,
    },
    OrderSubmitted {
        order_id: String,
        timestamp: DateTime<Utc>,
    },
    OrderShipped {
        order_id: String,
        tracking_code: String,
        timestamp: DateTime<Utc>,
    },
    OrderCancelled {
        order_id: String,
        reason: String,
        timestamp: DateTime<Utc>,
    },
}

// 事件溯源聚合 - src/domain/model/order.rs
#[derive(Debug, Clone)]
pub struct EventSourcedOrder {
    id: OrderId,
    customer_id: Option<CustomerId>,
    items: Vec<OrderItem>,
    status: OrderStatus,
    tracking_code: Option<String>,
    cancellation_reason: Option<String>,
    
    // 事件溯源特有的字段
    version: u64,
    uncommitted_events: Vec<OrderEvent>,
}

impl EventSourcedOrder {
    // 创建新订单
    pub fn create(id: OrderId, customer_id: CustomerId) -> Self {
        let mut order = Self {
            id,
            customer_id: Some(customer_id),
            items: Vec::new(),
            status: OrderStatus::Draft,
            tracking_code: None,
            cancellation_reason: None,
            version: 0,
            uncommitted_events: Vec::new(),
        };
        
        // 记录事件
        order.apply_new_event(OrderEvent::OrderCreated {
            order_id: order.id.to_string(),
            customer_id: customer_id.to_string(),
            timestamp: Utc::now(),
        });
        
        order
    }
    
    // 从历史事件重建
    pub fn from_events(id: OrderId, events: Vec<OrderEvent>) -> Result<Self, DomainError> {
        let mut order = Self {
            id,
            customer_id: None,
            items: Vec::new(),
            status: OrderStatus::Draft,
            tracking_code: None,
            cancellation_reason: None,
            version: 0,
            uncommitted_events: Vec::new(),
        };
        
        // 重放所有历史事件
        for event in events {
            order.apply_event(event)?;
            order.version += 1;
        }
        
        Ok(order)
    }
    
    // 添加商品
    pub fn add_item(&mut self, product_id: ProductId, quantity: u32, unit_price: Money) -> Result<(), DomainError> {
        // 业务规则验证
        if self.status != OrderStatus::Draft {
            return Err(DomainError::InvalidOrderState("Only draft orders can be modified".into()));
        }
        
        // 记录事件
        self.apply_new_event(OrderEvent::OrderItemAdded {
            order_id: self.id.to_string(),
            product_id: product_id.to_string(),
            quantity,
            unit_price: unit_price.value(),
            timestamp: Utc::now(),
        });
        
        Ok(())
    }
    
    // 提交订单
    pub fn submit(&mut self) -> Result<(), DomainError> {
        if self.status != OrderStatus::Draft {
            return Err(DomainError::InvalidOrderState("Only draft orders can be submitted".into()));
        }
        
        if self.items.is_empty() {
            return Err(DomainError::ValidationError("Cannot submit empty order".into()));
        }
        
        self.apply_new_event(OrderEvent::OrderSubmitted {
            order_id: self.id.to_string(),
            timestamp: Utc::now(),
        });
        
        Ok(())
    }
    
    // 应用新事件
    fn apply_new_event(&mut self, event: OrderEvent) {
        // 首先应用事件到状态
        self.apply_event(event.clone()).expect("Failed to apply new event");
        
        // 然后保存为未提交事件
        self.uncommitted_events.push(event);
        self.version += 1;
    }
    
    // 应用事件到状态
    fn apply_event(&mut self, event: OrderEvent) -> Result<(), DomainError> {
        match event {
            OrderEvent::OrderCreated { customer_id, .. } => {
                self.customer_id = Some(CustomerId::from_string(&customer_id)?);
                self.status = OrderStatus::Draft;
            },
            OrderEvent::OrderItemAdded { product_id, quantity, unit_price, .. } => {
                let item = OrderItem {
                    product_id: ProductId::from_string(&product_id)?,
                    quantity,
                    unit_price: Money::new(unit_price, Currency::USD)?,
                };
                self.items.push(item);
            },
            OrderEvent::OrderSubmitted { .. } => {
                self.status = OrderStatus::Submitted;
            },
            OrderEvent::OrderShipped { tracking_code, .. } => {
                self.status = OrderStatus::Shipped;
                self.tracking_code = Some(tracking_code);
            },
            OrderEvent::OrderCancelled { reason, .. } => {
                self.status = OrderStatus::Cancelled;
                self.cancellation_reason = Some(reason);
            },
        }
        
        Ok(())
    }
    
    // 获取未提交的事件
    pub fn uncommitted_events(&self) -> &[OrderEvent] {
        &self.uncommitted_events
    }
    
    // 清除未提交的事件
    pub fn clear_uncommitted_events(&mut self) {
        self.uncommitted_events.clear();
    }
    
    // Getters
    pub fn id(&self) -> &OrderId {
        &self.id
    }
    
    pub fn version(&self) -> u64 {
        self.version
    }
    
    // 其他getter和行为方法...
}

// 事件存储接口 - src/domain/repository/event_store.rs
#[async_trait]
pub trait EventStore {
    async fn append_events(
        &self, 
        stream_id: &str, 
        expected_version: u64, 
        events: &[OrderEvent]
    ) -> Result<u64, EventStoreError>;
    
    async fn load_events(&self, stream_id: &str) -> Result<Vec<OrderEvent>, EventStoreError>;
}

// 事件溯源仓储 - src/infrastructure/repository/event_sourced_order_repository.rs
pub struct EventSourcedOrderRepository {
    event_store: Arc<dyn EventStore>,
}

impl EventSourcedOrderRepository {
    pub fn new(event_store: Arc<dyn EventStore>) -> Self {
        Self { event_store }
    }
}

#[async_trait]
impl OrderRepository for EventSourcedOrderRepository {
    async fn save(&self, order: &EventSourcedOrder) -> Result<(), RepositoryError> {
        let uncommitted_events = order.uncommitted_events();
        if !uncommitted_events.is_empty() {
            // 保存新事件
            let stream_id = format!("order-{}", order.id());
            
            // 乐观并发控制
            let expected_version = order.version() - uncommitted_events.len() as u64;
            
            self.event_store.append_events(
                &stream_id, 
                expected_version, 
                uncommitted_events
            ).await.map_err(|e| RepositoryError::ConcurrencyError(e.to_string()))?;
            
            // 注意：通常这里会通过可变引用清除未提交事件
            // 但由于我们的接口使用不可变引用，这需要在调用方处理
        }
        
        Ok(())
    }
    
    async fn find_by_id(&self, id: &OrderId) -> Result<Option<EventSourcedOrder>, RepositoryError> {
        let stream_id = format!("order-{}", id);
        
        // 加载所有事件
        let events = match self.event_store.load_events(&stream_id).await {
            Ok(events) => events,
            Err(EventStoreError::StreamNotFound) => return Ok(None),
            Err(e) => return Err(RepositoryError::from(e)),
        };
        
        if events.is_empty() {
            return Ok(None);
        }
        
        // 从事件重建领域对象
        let order = EventSourcedOrder::from_events(id.clone(), events)
            .map_err(|e| RepositoryError::DomainError(e))?;
            
        Ok(Some(order))
    }
}
```

**事件溯源最佳实践**:

1. 使事件描述业务活动，而不仅仅是数据变化
2. 版本控制对于一致性至关重要，实现乐观并发控制
3. 考虑事件有效负载的向前兼容性，以适应模式变化
4. 为了性能建立快照，避免每次都重放所有事件
5. 使用投影创建针对查询优化的读模型
6. 在实体状态和事件之间保持双向一致性

### 微服务架构

微服务架构将系统分解为一组小型、自治的服务，每个服务专注于特定业务功能：

**架构特点**:

- **服务边界**: 通常围绕业务领域定义
- **独立部署**: 每个服务可独立开发、测试和部署
- **通信模式**: 通过API或消息进行服务间通信
- **数据所有权**: 每个服务拥有自己的数据存储

**Rust实现示例**:

```rust
// 产品目录服务 - 专注于产品管理
mod product_catalog {
    // 领域模型
    #[derive(Debug, Clone)]
    pub struct Product {
        id: ProductId,
        name: String,
        description: String,
        price: Money,
        category_id: CategoryId,
        attributes: HashMap<String, String>,
    }
    
    // API定义
    pub mod api {
        use tonic::{Request, Response, Status};
        use crate::proto::catalog::*;
        
        #[derive(Debug)]
        pub struct ProductCatalogService {
            service: Arc<ProductService>,
        }
        
        #[tonic::async_trait]
        impl catalog_server::Catalog for ProductCatalogService {
            async fn get_product(
                &self,
                request: Request<GetProductRequest>
            ) -> Result<Response<GetProductResponse>, Status> {
                let product_id = request.into_inner().id;
                
                let product = self.service.get_product(&product_id).await
                    .map_err(|e| Status::internal(e.to_string()))?
                    .ok_or_else(|| Status::not_found("Product not found"))?;
                
                Ok(Response::new(GetProductResponse {
                    product: Some(product.into()),
                }))
            }
            
            async fn search_products(
                &self,
                request: Request<SearchProductsRequest>
            ) -> Result<Response<SearchProductsResponse>, Status> {
                // 实现搜索逻辑
                todo!()
            }
            
            // 其他API方法...
        }
    }
}

// 订单服务 - 专注于订单处理
mod order_service {
    // 领域模型
    #[derive(Debug, Clone)]
    pub struct Order {
        id: OrderId,
        customer_id: CustomerId,
        items: Vec<OrderItem>,
        status: OrderStatus,
        // 订单相关字段...
    }
    
    // 外部服务客户端
    pub struct ProductCatalogClient {
        client: catalog_client::CatalogClient<tonic::transport::Channel>,
    }
    
    impl ProductCatalogClient {
        pub async fn new(addr: String) -> Result<Self, tonic::transport::Error> {
            let client = catalog_client::CatalogClient::connect(addr).await?;
            Ok(Self { client })
        }
        
        pub async fn get_product(&mut self, id: &str) -> Result<Option<Product>, ServiceError> {
            let request = tonic::Request::new(GetProductRequest {
                id: id.to_string(),
            });
            
            match self.client.get_product(request).await {
                Ok(response) => {
                    let proto_product = response.into_inner().product
                        .ok_or_else(|| ServiceError::UnexpectedResponse("Missing product in response".into()))?;
                        
                    Ok(Some(Product::from(proto_product)))
                }
                Err(status) if status.code() == tonic::Code::NotFound => Ok(None),
                Err(e) => Err(ServiceError::ExternalService(format!("Product catalog error: {}", e))),
            }
        }
    }
    
    // API实现
    pub mod api {
        use tonic::{Request, Response, Status};
        use crate::proto::orders::*;
        
        #[derive(Debug)]
        pub struct OrderService {
            service: Arc<OrderApplicationService>,
        }
        
        #[tonic::async_trait]
        impl orders_server::Orders for OrderService {
            async fn create_order(
                &self,
                request: Request<CreateOrderRequest>
            ) -> Result<Response<CreateOrderResponse>, Status> {
                // 实现订单创建逻辑
                todo!()
            }
            
            // 其他API方法...
        }
    }
}

// 服务发现与容错
pub struct ServiceRegistry {
    services: RwLock<HashMap<String, Vec<ServiceEndpoint>>>,
}

#[derive(Clone, Debug)]
pub struct ServiceEndpoint {
    url: String,
    health_status: HealthStatus,
    last_check: DateTime<Utc>,
}

impl ServiceRegistry {
    pub fn new() -> Self {
        Self {
            services: RwLock::new(HashMap::new()),
        }
    }
    
    pub async fn get_endpoint(&self, service_name: &str) -> Option<ServiceEndpoint> {
        let services = self.services.read().await;
        let endpoints = services.get(service_name)?;
        
        // 简单的轮询算法
        let healthy_endpoints: Vec<_> = endpoints.iter()
            .filter(|e| e.health_status == HealthStatus::Healthy)
            .collect();
            
        if healthy_endpoints.is_empty() {
            return None;
        }
        
        // 随机选择一个健康的端点
        let idx = rand::thread_rng().gen_range(0..healthy_endpoints.len());
        Some(healthy_endpoints[idx].clone())
    }
    
    // 其他服务注册、健康检查方法...
}

// 断路器实现
pub struct CircuitBreaker<T> {
    inner: T,
    state: RwLock<CircuitState>,
    failure_threshold: u32,
    reset_timeout: Duration,
}

enum CircuitState {
    Closed { failures: u32 },
    Open { until: DateTime<Utc> },
    HalfOpen,
}

impl<T> CircuitBreaker<T> {
    pub fn new(inner: T, failure_threshold: u32, reset_timeout: Duration) -> Self {
        Self {
            inner,
            state: RwLock::new(CircuitState::Closed { failures: 0 }),
            failure_threshold,
            reset_timeout,
        }
    }
}

#[async_trait]
impl<T: ProductCatalogService + Send + Sync> ProductCatalogService for CircuitBreaker<T> {
    async fn get_product(&self, id: &str) -> Result<Option<Product>, ServiceError> {
        // 检查断路器状态
        {
            let state = self.state.read().await;
            match &*state {
                CircuitState::Open { until } if *until > Utc::now() => {
                    return Err(ServiceError::CircuitBreakerOpen);
                }
                CircuitState::Open { .. } => {
                    // 重置超时，尝试半开状态
                    drop(state);
                    let mut state = self.state.write().await;
                    *state = CircuitState::HalfOpen;
                },
                _ => {}
            }
        }
        
        // 尝试执行操作
        match self.inner.get_product(id).await {
            Ok(result) => {
                // 成功，重置失败计数
                if let CircuitState::HalfOpen = *self.state.read().await {
                    let mut state = self.state.write().await;
                    *state = CircuitState::Closed { failures: 0 };
                }
                Ok(result)
            }
            Err(e) => {
                // 失败，更新断路器状态
                let mut state = self.state.write().await;
                match &mut *state {
                    CircuitState::Closed { failures } => {
                        *failures += 1;
                        if *failures >= self.failure_threshold {
                            *state = CircuitState::Open { 
                                until: Utc::now() + self.reset_timeout
                            };
                        }
                    }
                    CircuitState::HalfOpen => {
                        *state = CircuitState::Open { 
                            until: Utc::now() + self.reset_timeout
                        };
                    }
                    CircuitState::Open { .. } => {} // 已经打开
                }
                Err(e)
            }
        }
    }
    
    // 实现其他方法...
}
```

**微服务最佳实践**:

1. 围绕业务能力设计服务边界，而不仅仅是技术层
2. 尽量减少服务间同步通信，考虑使用事件驱动模型
3. 实现强大的监控、日志和分布式追踪
4. 使用断路器和重试机制提高系统弹性
5. 为每个服务实现独立的CI/CD流程
6. 进行契约测试确保服务间接口兼容性

### 分布式事务处理

在微服务架构中，跨服务事务是一个常见挑战，Saga模式和两阶段提交是常见解决方案：

**Saga模式**:

```rust
// Saga协调器
pub struct OrderSaga {
    order_service: Arc<dyn OrderService>,
    inventory_service: Arc<dyn InventoryService>,
    payment_service: Arc<dyn PaymentService>,
    shipping_service: Arc<dyn ShippingService>,
}

impl OrderSaga {
    pub async fn process_order(&self, order_id: &OrderId) -> Result<(), SagaError> {
        // Step 1: 验证订单
        let order = self.order_service.get_order(order_id).await?
            .ok_or(SagaError::OrderNotFound)?;
            
        // Step 2: 预留库存
        match self.inventory_service.reserve_inventory(&order).await {
            Ok(_) => {},
            Err(e) => {
                // 库存预留失败，不需要补偿操作，直接返回错误
                return Err(SagaError::InventoryError(e));
            }
        };
        
        // Step 3: 处理支付
        match self.payment_service.process_payment(&order).await {
            Ok(_) => {},
            Err(e) => {
                // 支付失败，补偿操作：释放库存
                self.inventory_service.release_inventory(&order).await
                    .unwrap_or_else(|e| {
                        // 补偿操作失败，记录但继续
                        tracing::error!("Compensation failed: {}", e);
                    });
                    
                return Err(SagaError::PaymentError(e));
            }
        };
        
        // Step 4: 创建物流单
        match self.shipping_service.create_shipment(&order).await {
            Ok(_) => {},
            Err(e) => {
                // 物流创建失败，补偿操作：退款和释放库存
                self.payment_service.refund(&order).await
                    .unwrap_or_else(|e| {
                        tracing::error!("Payment refund failed: {}", e);
                    });
                    
                self.inventory_service.release_inventory(&order).await
                    .unwrap_or_else(|e| {
                        tracing::error!("Inventory release failed: {}", e);
                    });
                    
                return Err(SagaError::ShippingError(e));
            }
        };
        
        // Step 5: 完成订单
        match self.order_service.complete_order(order_id).await {
            Ok(_) => {},
            Err(e) => {
                // 订单完成失败，但前面的步骤已成功，记录错误但不回滚
                tracing::error!("Failed to complete order: {}", e);
                // 可以触发人工介入或其他机制
            }
        };
        
        Ok(())
    }
}
```

**更高级的基于事件的Saga实现**:

```rust
// Saga状态机
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "status")]
pub enum OrderProcessSaga {
    Started {
        order_id: String,
        step: OrderSagaStep,
        compensation_steps: Vec<OrderSagaCompensationStep>,
    },
    Completed {
        order_id: String,
    },
    Failed {
        order_id: String,
        error: String,
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum OrderSagaStep {
    ValidateOrder,
    ReserveInventory,
    ProcessPayment,
    CreateShipment,
    CompleteOrder,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OrderSagaCompensationStep {
    ReleaseInventory,
    RefundPayment,
    CancelShipment,
}

// 事件驱动的Saga协调器
pub struct EventDrivenSagaCoordinator {
    event_publisher: Arc<dyn EventPublisher>,
    saga_repository: Arc<dyn SagaRepository>,
}

impl EventDrivenSagaCoordinator {
    pub async fn start_order_saga(&self, order_id: &OrderId) -> Result<(), SagaError> {
        // 创建saga状态
        let saga = OrderProcessSaga::Started {
            order_id: order_id.to_string(),
            step: OrderSagaStep::ValidateOrder,
            compensation_steps: Vec::new(),
        };
        
        // 保存saga状态
        self.saga_repository.save(&saga).await?;
        
        // 发布启动事件
        self.event_publisher.publish(
            "order-saga",
            &SagaEvent::Started {
                saga_id: format!("order-{}", order_id),
                order_id: order_id.to_string(),
            }
        ).await?;
        
        Ok(())
    }
    
    // 处理验证订单事件
    pub async fn handle_validate_order_event

```rust
    // 处理验证订单事件
    pub async fn handle_validate_order_event(
        &self,
        event: &OrderValidatedEvent
    ) -> Result<(), SagaError> {
        // 获取当前saga状态
        let saga_id = format!("order-{}", event.order_id);
        let saga = self.saga_repository.find_by_id(&saga_id).await?
            .ok_or(SagaError::SagaNotFound(saga_id.clone()))?;
            
        // 更新saga状态
        match saga {
            OrderProcessSaga::Started { order_id, step, mut compensation_steps } => {
                if step != OrderSagaStep::ValidateOrder {
                    return Err(SagaError::UnexpectedStep(format!(
                        "Expected step {:?}, got {:?}", 
                        OrderSagaStep::ValidateOrder, 
                        step
                    )));
                }
                
                // 更新状态为下一步
                let updated_saga = OrderProcessSaga::Started {
                    order_id,
                    step: OrderSagaStep::ReserveInventory,
                    compensation_steps,
                };
                
                // 保存更新后的saga
                self.saga_repository.save(&updated_saga).await?;
                
                // 发布库存预留事件
                self.event_publisher.publish(
                    "inventory-commands",
                    &InventoryCommand::ReserveItems {
                        saga_id: saga_id.clone(),
                        order_id: event.order_id.clone(),
                        items: event.items.clone(),
                    }
                ).await?;
                
                Ok(())
            },
            OrderProcessSaga::Completed { .. } => {
                Err(SagaError::SagaAlreadyCompleted(saga_id))
            },
            OrderProcessSaga::Failed { .. } => {
                Err(SagaError::SagaAlreadyFailed(saga_id))
            }
        }
    }
    
    // 处理库存预留事件
    pub async fn handle_inventory_reserved_event(
        &self,
        event: &InventoryReservedEvent
    ) -> Result<(), SagaError> {
        // 获取当前saga状态
        let saga_id = event.saga_id.clone();
        let saga = self.saga_repository.find_by_id(&saga_id).await?
            .ok_or(SagaError::SagaNotFound(saga_id.clone()))?;
            
        // 更新saga状态
        match saga {
            OrderProcessSaga::Started { order_id, step, mut compensation_steps } => {
                if step != OrderSagaStep::ReserveInventory {
                    return Err(SagaError::UnexpectedStep(format!(
                        "Expected step {:?}, got {:?}", 
                        OrderSagaStep::ReserveInventory, 
                        step
                    )));
                }
                
                // 添加补偿步骤
                compensation_steps.push(OrderSagaCompensationStep::ReleaseInventory);
                
                // 更新状态为下一步
                let updated_saga = OrderProcessSaga::Started {
                    order_id: order_id.clone(),
                    step: OrderSagaStep::ProcessPayment,
                    compensation_steps,
                };
                
                // 保存更新后的saga
                self.saga_repository.save(&updated_saga).await?;
                
                // 发布支付处理事件
                self.event_publisher.publish(
                    "payment-commands",
                    &PaymentCommand::ProcessPayment {
                        saga_id: saga_id.clone(),
                        order_id,
                        amount: event.total_amount.clone(),
                    }
                ).await?;
                
                Ok(())
            },
            OrderProcessSaga::Completed { .. } => {
                Err(SagaError::SagaAlreadyCompleted(saga_id))
            },
            OrderProcessSaga::Failed { .. } => {
                Err(SagaError::SagaAlreadyFailed(saga_id))
            }
        }
    }
    
    // 处理库存预留失败事件
    pub async fn handle_inventory_reservation_failed_event(
        &self,
        event: &InventoryReservationFailedEvent
    ) -> Result<(), SagaError> {
        // 获取当前saga状态
        let saga_id = event.saga_id.clone();
        let saga = self.saga_repository.find_by_id(&saga_id).await?
            .ok_or(SagaError::SagaNotFound(saga_id.clone()))?;
            
        // 更新saga状态为失败
        match saga {
            OrderProcessSaga::Started { order_id, .. } => {
                let failed_saga = OrderProcessSaga::Failed {
                    order_id,
                    error: format!("库存预留失败: {}", event.reason),
                };
                
                // 保存失败状态
                self.saga_repository.save(&failed_saga).await?;
                
                // 不需要补偿操作，因为这是第一步失败
                
                Ok(())
            },
            _ => Ok(()) // 已经完成或失败，忽略
        }
    }
    
    // 其他事件处理方法...
}
```

**分布式事务最佳实践**:

1. 使用Saga模式处理复杂的跨服务事务
2. 确保每个补偿操作是幂等的，可以安全重试
3. 实现事务日志以跟踪分布式事务的状态
4. 为长时间运行的事务设计超时和恢复机制
5. 尽可能简化事务涉及的服务数量，减少失败可能性
6. 考虑使用状态机模式精确跟踪和管理事务进度

## 8. 工程实践案例

### 电子商务系统示例

下面是一个电子商务系统的关键部分设计，演示如何将概念模型映射到Rust实现：

**概念模型与核心领域对象**:

```rust
// src/domain/model/product.rs
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProductId(Uuid);

#[derive(Debug, Clone)]
pub struct Product {
    id: ProductId,
    name: String,
    description: String,
    price: Money,
    inventory: InventoryInfo,
    status: ProductStatus,
    category_id: CategoryId,
}

#[derive(Debug, Clone)]
pub struct InventoryInfo {
    available_quantity: u32,
    reserved_quantity: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProductStatus {
    Draft,
    Active,
    Discontinued,
}

impl Product {
    pub fn new(
        id: ProductId,
        name: String,
        description: String,
        price: Money,
        initial_quantity: u32,
        category_id: CategoryId,
    ) -> Result<Self, DomainError> {
        // 验证业务规则
        if name.is_empty() {
            return Err(DomainError::ValidationError("Product name cannot be empty".into()));
        }
        
        if price.is_zero() || price.is_negative() {
            return Err(DomainError::ValidationError("Product price must be positive".into()));
        }
        
        Ok(Self {
            id,
            name,
            description,
            price,
            inventory: InventoryInfo {
                available_quantity: initial_quantity,
                reserved_quantity: 0,
            },
            status: ProductStatus::Draft,
            category_id,
        })
    }
    
    pub fn activate(&mut self) -> Result<(), DomainError> {
        match self.status {
            ProductStatus::Draft => {
                self.status = ProductStatus::Active;
                Ok(())
            }
            ProductStatus::Active => Ok(()),
            ProductStatus::Discontinued => {
                Err(DomainError::InvalidStateTransition("Cannot activate a discontinued product".into()))
            }
        }
    }
    
    pub fn update_price(&mut self, new_price: Money) -> Result<(), DomainError> {
        if new_price.is_zero() || new_price.is_negative() {
            return Err(DomainError::ValidationError("Product price must be positive".into()));
        }
        
        self.price = new_price;
        Ok(())
    }
    
    pub fn reserve_inventory(&mut self, quantity: u32) -> Result<(), DomainError> {
        if self.status != ProductStatus::Active {
            return Err(DomainError::InvalidStateForOperation(
                "Only active products can be reserved".into()
            ));
        }
        
        if quantity > self.inventory.available_quantity {
            return Err(DomainError::InsufficientInventory {
                requested: quantity,
                available: self.inventory.available_quantity,
            });
        }
        
        self.inventory.available_quantity -= quantity;
        self.inventory.reserved_quantity += quantity;
        
        Ok(())
    }
    
    pub fn commit_reservation(&mut self, quantity: u32) -> Result<(), DomainError> {
        if quantity > self.inventory.reserved_quantity {
            return Err(DomainError::ValidationError(
                format!("Cannot commit more than reserved: {} > {}", 
                        quantity, self.inventory.reserved_quantity)
            ));
        }
        
        self.inventory.reserved_quantity -= quantity;
        
        Ok(())
    }
    
    pub fn cancel_reservation(&mut self, quantity: u32) -> Result<(), DomainError> {
        if quantity > self.inventory.reserved_quantity {
            return Err(DomainError::ValidationError(
                format!("Cannot cancel more than reserved: {} > {}", 
                        quantity, self.inventory.reserved_quantity)
            ));
        }
        
        self.inventory.reserved_quantity -= quantity;
        self.inventory.available_quantity += quantity;
        
        Ok(())
    }
    
    // Getters
    pub fn id(&self) -> &ProductId {
        &self.id
    }
    
    pub fn name(&self) -> &str {
        &self.name
    }
    
    pub fn price(&self) -> &Money {
        &self.price
    }
    
    pub fn available_quantity(&self) -> u32 {
        self.inventory.available_quantity
    }
    
    pub fn status(&self) -> &ProductStatus {
        &self.status
    }
}

// src/domain/model/order.rs
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrderId(Uuid);

#[derive(Debug, Clone)]
pub struct Order {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    status: OrderStatus,
    shipping_address: Address,
    total_amount: Money,
    created_at: DateTime<Utc>,
    last_modified_at: DateTime<Utc>,
}

#[derive(Debug, Clone)]
pub struct OrderItem {
    product_id: ProductId,
    product_name: String,
    quantity: u32,
    unit_price: Money,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OrderStatus {
    Draft,
    Submitted,
    Paid,
    Shipped,
    Delivered,
    Cancelled,
}

impl Order {
    pub fn new(
        id: OrderId,
        customer_id: CustomerId,
        shipping_address: Address,
    ) -> Self {
        let now = Utc::now();
        Self {
            id,
            customer_id,
            items: Vec::new(),
            status: OrderStatus::Draft,
            shipping_address,
            total_amount: Money::zero(Currency::USD),
            created_at: now,
            last_modified_at: now,
        }
    }
    
    pub fn add_item(
        &mut self,
        product_id: ProductId,
        product_name: String,
        quantity: u32,
        unit_price: Money,
    ) -> Result<(), DomainError> {
        if self.status != OrderStatus::Draft {
            return Err(DomainError::InvalidStateForOperation(
                "Items can only be added to draft orders".into()
            ));
        }
        
        if quantity == 0 {
            return Err(DomainError::ValidationError("Quantity must be greater than zero".into()));
        }
        
        // 检查是否已存在该商品
        for item in &mut self.items {
            if item.product_id == product_id {
                // 更新已有商品
                item.quantity += quantity;
                self.recalculate_total();
                self.last_modified_at = Utc::now();
                return Ok(());
            }
        }
        
        // 添加新商品
        let item = OrderItem {
            product_id,
            product_name,
            quantity,
            unit_price,
        };
        
        self.items.push(item);
        self.recalculate_total();
        self.last_modified_at = Utc::now();
        
        Ok(())
    }
    
    pub fn remove_item(&mut self, product_id: &ProductId) -> Result<(), DomainError> {
        if self.status != OrderStatus::Draft {
            return Err(DomainError::InvalidStateForOperation(
                "Items can only be removed from draft orders".into()
            ));
        }
        
        let original_len = self.items.len();
        self.items.retain(|item| item.product_id != *product_id);
        
        if self.items.len() == original_len {
            return Err(DomainError::EntityNotFound(format!("Product not found in order: {:?}", product_id)));
        }
        
        self.recalculate_total();
        self.last_modified_at = Utc::now();
        
        Ok(())
    }
    
    pub fn submit(&mut self) -> Result<(), DomainError> {
        if self.status != OrderStatus::Draft {
            return Err(DomainError::InvalidStateTransition(
                format!("Cannot submit order in status: {:?}", self.status)
            ));
        }
        
        if self.items.is_empty() {
            return Err(DomainError::ValidationError("Cannot submit empty order".into()));
        }
        
        self.status = OrderStatus::Submitted;
        self.last_modified_at = Utc::now();
        
        Ok(())
    }
    
    pub fn mark_as_paid(&mut self) -> Result<(), DomainError> {
        if self.status != OrderStatus::Submitted {
            return Err(DomainError::InvalidStateTransition(
                format!("Cannot mark as paid order in status: {:?}", self.status)
            ));
        }
        
        self.status = OrderStatus::Paid;
        self.last_modified_at = Utc::now();
        
        Ok(())
    }
    
    pub fn cancel(&mut self, reason: &str) -> Result<(), DomainError> {
        match self.status {
            OrderStatus::Draft | OrderStatus::Submitted | OrderStatus::Paid => {
                self.status = OrderStatus::Cancelled;
                self.last_modified_at = Utc::now();
                Ok(())
            },
            _ => Err(DomainError::InvalidStateTransition(
                format!("Cannot cancel order in status: {:?}", self.status)
            )),
        }
    }
    
    fn recalculate_total(&mut self) {
        let mut total = Money::zero(Currency::USD);
        
        for item in &self.items {
            // 计算每个商品小计
            let subtotal = item.unit_price.multiply(item.quantity as f64)
                .expect("Multiplication should not fail with positive quantities");
                
            // 累加到总金额
            total = total.add(&subtotal)
                .expect("Addition of same currency should not fail");
        }
        
        self.total_amount = total;
    }
    
    // Getters
    pub fn id(&self) -> &OrderId {
        &self.id
    }
    
    pub fn status(&self) -> &OrderStatus {
        &self.status
    }
    
    pub fn items(&self) -> &[OrderItem] {
        &self.items
    }
    
    pub fn total_amount(&self) -> &Money {
        &self.total_amount
    }
}
```

**应用服务层**:

```rust
// src/application/product_service.rs
pub struct ProductService {
    product_repository: Arc<dyn ProductRepository>,
    event_publisher: Arc<dyn EventPublisher>,
}

impl ProductService {
    pub fn new(
        product_repository: Arc<dyn ProductRepository>,
        event_publisher: Arc<dyn EventPublisher>,
    ) -> Self {
        Self {
            product_repository,
            event_publisher,
        }
    }
    
    pub async fn create_product(
        &self,
        command: CreateProductCommand,
    ) -> Result<ProductId, ApplicationError> {
        // 业务逻辑验证
        if command.name.is_empty() {
            return Err(ApplicationError::ValidationError("Product name cannot be empty".into()));
        }
        
        // 创建领域对象
        let product_id = ProductId::new();
        
        let price = Money::new(command.price, Currency::USD)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        let category_id = CategoryId::from_string(&command.category_id)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        let product = Product::new(
            product_id.clone(),
            command.name,
            command.description,
            price,
            command.initial_quantity,
            category_id,
        ).map_err(ApplicationError::from)?;
        
        // 持久化
        self.product_repository.save(&product).await
            .map_err(ApplicationError::from)?;
            
        // 发布事件
        let event = ProductCreatedEvent {
            product_id: product_id.to_string(),
            name: product.name().to_string(),
            price: product.price().value(),
            timestamp: Utc::now(),
        };
        
        self.event_publisher.publish("product-events", &event).await
            .map_err(|e| ApplicationError::EventPublishingError(e.to_string()))?;
            
        Ok(product_id)
    }
    
    pub async fn update_product_price(
        &self,
        command: UpdateProductPriceCommand,
    ) -> Result<(), ApplicationError> {
        // 获取产品
        let product_id = ProductId::from_string(&command.product_id)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        let mut product = self.product_repository.find_by_id(&product_id).await
            .map_err(ApplicationError::from)?
            .ok_or(ApplicationError::EntityNotFound(format!("Product not found: {}", command.product_id)))?;
            
        // 更新价格
        let new_price = Money::new(command.new_price, Currency::USD)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        product.update_price(new_price)
            .map_err(ApplicationError::from)?;
            
        // 持久化
        self.product_repository.save(&product).await
            .map_err(ApplicationError::from)?;
            
        // 发布事件
        let event = ProductPriceUpdatedEvent {
            product_id: product_id.to_string(),
            old_price: command.old_price,
            new_price: command.new_price,
            timestamp: Utc::now(),
        };
        
        self.event_publisher.publish("product-events", &event).await
            .map_err(|e| ApplicationError::EventPublishingError(e.to_string()))?;
            
        Ok(())
    }
    
    // 其他产品服务方法...
}

// src/application/order_service.rs
pub struct OrderService {
    order_repository: Arc<dyn OrderRepository>,
    product_repository: Arc<dyn ProductRepository>,
    event_publisher: Arc<dyn EventPublisher>,
}

impl OrderService {
    pub fn new(
        order_repository: Arc<dyn OrderRepository>,
        product_repository: Arc<dyn ProductRepository>,
        event_publisher: Arc<dyn EventPublisher>,
    ) -> Self {
        Self {
            order_repository,
            product_repository,
            event_publisher,
        }
    }
    
    pub async fn create_order(
        &self,
        command: CreateOrderCommand,
    ) -> Result<OrderId, ApplicationError> {
        // 验证客户ID
        let customer_id = CustomerId::from_string(&command.customer_id)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        // 验证地址
        if command.shipping_address.is_empty() {
            return Err(ApplicationError::ValidationError("Shipping address cannot be empty".into()));
        }
        
        // 创建订单
        let order_id = OrderId::new();
        let address = Address::new(
            command.shipping_address.street,
            command.shipping_address.city,
            command.shipping_address.state,
            command.shipping_address.country,
            command.shipping_address.postal_code,
        ).map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
        
        let mut order = Order::new(order_id.clone(), customer_id, address);
        
        // 持久化
        self.order_repository.save(&order).await
            .map_err(ApplicationError::from)?;
            
        // 发布事件
        let event = OrderCreatedEvent {
            order_id: order_id.to_string(),
            customer_id: customer_id.to_string(),
            timestamp: Utc::now(),
        };
        
        self.event_publisher.publish("order-events", &event).await
            .map_err(|e| ApplicationError::EventPublishingError(e.to_string()))?;
            
        Ok(order_id)
    }
    
    pub async fn add_order_item(
        &self,
        command: AddOrderItemCommand,
    ) -> Result<(), ApplicationError> {
        // 获取订单
        let order_id = OrderId::from_string(&command.order_id)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        let mut order = self.order_repository.find_by_id(&order_id).await
            .map_err(ApplicationError::from)?
            .ok_or(ApplicationError::EntityNotFound(format!("Order not found: {}", command.order_id)))?;
            
        // 获取产品信息
        let product_id = ProductId::from_string(&command.product_id)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        let product = self.product_repository.find_by_id(&product_id).await
            .map_err(ApplicationError::from)?
            .ok_or(ApplicationError::EntityNotFound(format!("Product not found: {}", command.product_id)))?;
            
        // 验证库存
        if product.available_quantity() < command.quantity {
            return Err(ApplicationError::BusinessRuleViolation(
                format!("Insufficient inventory: requested {}, available {}", 
                        command.quantity, product.available_quantity())
            ));
        }
        
        // 添加订单项
        order.add_item(
            product_id,
            product.name().to_string(),
            command.quantity,
            product.price().clone(),
        ).map_err(ApplicationError::from)?;
        
        // 持久化订单
        self.order_repository.save(&order).await
            .map_err(ApplicationError::from)?;
            
        // 发布事件
        let event = OrderItemAddedEvent {
            order_id: order_id.to_string(),
            product_id: product_id.to_string(),
            product_name: product.name().to_string(),
            quantity: command.quantity,
            unit_price: product.price().value(),
            timestamp: Utc::now(),
        };
        
        self.event_publisher.publish("order-events", &event).await
            .map_err(|e| ApplicationError::EventPublishingError(e.to_string()))?;
            
        Ok(())
    }
    
    pub async fn submit_order(
        &self,
        command: SubmitOrderCommand,
    ) -> Result<(), ApplicationError> {
        // 获取订单
        let order_id = OrderId::from_string(&command.order_id)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        let mut order = self.order_repository.find_by_id(&order_id).await
            .map_err(ApplicationError::from)?
            .ok_or(ApplicationError::EntityNotFound(format!("Order not found: {}", command.order_id)))?;
            
        // 提交订单
        order.submit().map_err(ApplicationError::from)?;
        
        // 持久化
        self.order_repository.save(&order).await
            .map_err(ApplicationError::from)?;
            
        // 发布事件
        let event = OrderSubmittedEvent {
            order_id: order_id.to_string(),
            total_amount: order.total_amount().value(),
            timestamp: Utc::now(),
        };
        
        self.event_publisher.publish("order-events", &event).await
            .map_err(|e| ApplicationError::EventPublishingError(e.to_string()))?;
            
        Ok(())
    }
    
    // 其他订单服务方法...
}
```

**接口层（HTTP API）**:

```rust
// src/interfaces/http/product_controller.rs
pub struct ProductController {
    product_service: Arc<ProductService>,
}

impl ProductController {
    pub fn new(product_service: Arc<ProductService>) -> Self {
        Self { product_service }
    }
    
    pub async fn create_product(
        &self,
        req: HttpRequest,
        body: web::Json<CreateProductRequest>,
    ) -> Result<HttpResponse, ApiError> {
        // 转换请求到命令
        let command = CreateProductCommand {
            name: body.name.clone(),
            description: body.description.clone(),
            price: body.price,
            initial_quantity: body.initial_quantity,
            category_id: body.category_id.clone(),
        };
        
        // 处理命令
        let product_id = self.product_service.create_product(command).await
            .map_err(ApiError::from)?;
            
        // 构建响应
        let response = CreateProductResponse {
            product_id: product_id.to_string(),
            message: "Product created successfully".to_string(),
        };
        
        Ok(HttpResponse::Created().json(response))
    }
    
    pub async fn update_product_price(
        &self,
        path: web::Path<String>,
        body: web::Json<UpdateProductPriceRequest>,
    ) -> Result<HttpResponse, ApiError> {
        let product_id = path.into_inner();
        
        // 检查价格是否真的变化了
        if body.old_price == body.new_price {
            return Ok(HttpResponse::Ok().json(ApiResponse {
                message: "No price change detected".to_string(),
            }));
        }
        
        // 转换请求到命令
        let command = UpdateProductPriceCommand {
            product_id,
            old_price: body.old_price,
            new_price: body.new_price,
        };
        
        // 处理命令
        self.product_service.update_product_price(command).await
            .map_err(ApiError::from)?;
            
        // 构建响应
        Ok(HttpResponse::Ok().json(ApiResponse {
            message: "Product price updated successfully".to_string(),
        }))
    }
    
    pub async fn get_product(
        &self,
        path: web::Path<String>,
    ) -> Result<HttpResponse, ApiError> {
        let product_id = path.into_inner();
        
        // 转换为领域ID
        let domain_id = ProductId::from_string(&product_id)
            .map_err(|e| ApiError::ValidationError(e.to_string()))?;
            
        // 查询产品
        let product = self.product_service.get_product(&domain_id).await
            .map_err(ApiError::from)?
            .ok_or_else(|| ApiError::ResourceNotFound(format!("Product not found: {}", product_id)))?;
            
        // 转换为响应DTO
        let response = ProductResponse {
            id: product.id().to_string(),
            name: product.name().to_string(),
            description: product.description().to_string(),
            price: product.price().value(),
            available_quantity: product.available_quantity(),
            status: format!("{:?}", product.status()),
        };
        
        Ok(HttpResponse::Ok().json(response))
    }
    
    // 其他控制器方法...
}

// 配置路由
pub fn configure_routes(cfg: &mut web::ServiceConfig) {
    cfg.service(
        web::scope("/api/products")
            .route("", web::post().to(ProductController::create_product))
            .route("/{id}", web::get().to(ProductController::get_product))
            .route("/{id}/price", web::put().to(ProductController::update_product_price))
    );
}
```

**基础设施层（数据存储）**:

```rust
// src/infrastructure/persistence/postgres/product_repository.rs
pub struct PostgresProductRepository {
    pool: PgPool,
}

impl PostgresProductRepository {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
}

#[async_trait]
impl ProductRepository for PostgresProductRepository {
    async fn save(&self, product: &Product) -> Result<(), RepositoryError> {
        // 开始事务
        let mut tx = self.pool.begin().await
            .map_err(|e| RepositoryError::ConnectionError(e.to_string()))?;
            
        // 检查是否已存在（决定是更新还是插入）
        let exists = sqlx::query!(
            "SELECT 1 FROM products WHERE id = $1",
            product.id().to_string()
        )
        .fetch_optional(&mut *tx)
        .await
        .map_err(|e| RepositoryError::QueryError(e.to_string()))?
        .is_some();
        
        if exists {
            // 更新
            sqlx::query!(
                r#"
                UPDATE products 
                SET name = $1, 
                    description = $2, 
                    price = $3, 
                    available_quantity = $4,
                    reserved_quantity = $5,
                    status = $6,
                    category_id = $7,
                    updated_at = NOW()
                WHERE id = $8
                "#,
                product.name(),
                product.description(),
                product.price().value() as f64,
                product.available_quantity() as i32,
                product.reserved_quantity() as i32,
                product.status().to_string(),
                product.category_id().to_string(),
                product.id().to_string(),
            )
            .execute(&mut *tx)
            .await
            .map_err(|e| RepositoryError::QueryError(e.to_string()))?;
        } else {
            // 插入
            sqlx::query!(
                r#"
                INSERT INTO products (
                    id, name, description, price, 
                    available_quantity, reserved_quantity, 
                    status, category_id, created_at, updated_at
                ) VALUES (
                    $1, $2, $3, $4, $5, $6, $7, $8, NOW(), NOW()
                )
                "#,
                product.id().to_string(),
                product.name(),
                product.description(),
                product.price().value() as f64,
                product.available_quantity() as i32,
                product.reserved_quantity() as i32,
                product.status().to_string(),
                product.category_id().to_string(),
            )
            .execute(&mut *tx)
            .await
            .map_err(|e| RepositoryError::QueryError(e.to_string()))?;
        }
        
        // 提交事务
        tx.commit().await
            .map_err(|e| RepositoryError::ConnectionError(e.to_string()))?;
            
        Ok(())
    }
    
    async fn find_by_id(&self, id: &ProductId) -> Result<Option<Product>, RepositoryError> {
        let row = sqlx::query!(
            r#"
            SELECT 
                id, name, description, price, 
                available_quantity, reserved_quantity, 
                status, category_id, 
                created_at, updated_at
            FROM products 
            WHERE id = $1
            "#,
            id.to_string()
        )
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| RepositoryError::QueryError(e.to_string()))?;
        
        match row {
            Some(row) => {
                // 将数据库记录映射到领域对象
                let product_id = ProductId::from_string(&row.id)
                    .map_err(|e| RepositoryError::DataError(e.to_string()))?;
                    
                let category_id = CategoryId::from_string(&row.category_id)
                    .map_err(|e| RepositoryError::DataError(e.to_string()))?;
                    
                let price = Money::new(row.price as f64, Currency::USD)
                    .map_err(|e| RepositoryError::DataError(e.to_string()))?;
                    
                let status = match row.status.as_str() {
                    "Draft" => ProductStatus::Draft,
                    "Active" => ProductStatus::Active,
                    "Discontinued" => ProductStatus::Discontinued,
                    _ => return Err(RepositoryError::DataError(
                        format!("Unknown product status: {}", row.status)
                    )),
                };
                
                let product = Product::from_persistence(
                    product_id,
                    row.name,
                    row.description,
                    price,
                    row.available_quantity as u32,
                    row.reserved_quantity as u32,
                    status,
                    category_id,
                );
                
                Ok(Some(product))
            },
            None => Ok(None),
        }
    }
    
    // 其他仓储方法...
}
```

**主应用组装**:

```rust
// src/main.rs
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 加载配置
    let config = AppConfig::load()?;
    
    // 初始化日志
    init_logging(&config.logging)?;
    
    // 数据库连接
    let db_pool = PgPoolOptions::new()
        .max_connections(config.database.max_connections)
        .connect(&config.database.url)
        .await?;
        
    // 初始化仓储
    let product_repository = Arc::new(PostgresProductRepository::new(db_pool.clone()));
    let order_repository = Arc::new(PostgresOrderRepository::new(db_pool.clone()));
    
    // 初始化消息发布者
    let event_publisher = match config.event_publisher.kind.as_str() {
        "kafka" => {
            let kafka_config = KafkaConfig {
                bootstrap_servers: config.event_publisher.kafka.bootstrap_servers.clone(),
                client_id: config.event_publisher.kafka.client_id.clone(),
            };
            Arc::new(KafkaEventPublisher::new(kafka_config).await?)
        },
        "redis" => {
            let redis_config = RedisConfig {
                url: config.event_publisher.redis.url.clone(),
            };
            Arc::new(RedisEventPublisher::new(redis_config).await?)
        },
        _ => Arc::new(InMemoryEventPublisher::new()),
    };
    
    // 初始化应用服务
    let product_service = Arc::new(ProductService::new(
        product_repository.clone(),
        event_publisher.clone(),
    ));
    
    let order_service = Arc::new(OrderService::new(
        order_repository.clone(),
        product_repository.clone(),
        event_publisher.clone(),
    ));
    
    // 初始化控制器
    let product_controller = web::Data::new(ProductController::new(product_service.clone()));
    let order_controller = web::Data::new(OrderController::new(order_service.clone()));
    
    // 启动HTTP服务器
    tracing::info!(
        address =

```rust
    // 启动HTTP服务器
    tracing::info!(
        address = %format!("{}:{}", config.server.host, config.server.port),
        "Starting HTTP server"
    );
    
    HttpServer::new(move || {
        App::new()
            .app_data(product_controller.clone())
            .app_data(order_controller.clone())
            .wrap(Logger::default())
            .wrap(Cors::default()
                .allowed_origin("http://localhost:3000")
                .allowed_methods(vec!["GET", "POST", "PUT", "DELETE"])
                .allowed_headers(vec![http::header::AUTHORIZATION, http::header::CONTENT_TYPE])
                .max_age(3600)
            )
            .configure(interfaces::http::product_routes::configure_routes)
            .configure(interfaces::http::order_routes::configure_routes)
            .default_service(web::route().to(|| HttpResponse::NotFound()))
    })
    .bind(format!("{}:{}", config.server.host, config.server.port))?
    .run()
    .await?;
    
    Ok(())
}
```

### 实时库存管理系统

以下是一个实时库存管理系统的设计，演示如何处理高并发和数据一致性：

**领域模型设计**:

```rust
// src/domain/model/inventory.rs
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InventoryItemId(Uuid);

#[derive(Debug, Clone)]
pub struct InventoryItem {
    id: InventoryItemId,
    product_id: ProductId,
    warehouse_id: WarehouseId,
    quantity: u32,
    reserved: u32,
    version: u64, // 用于乐观锁
    last_updated: DateTime<Utc>,
}

impl InventoryItem {
    pub fn new(
        id: InventoryItemId,
        product_id: ProductId,
        warehouse_id: WarehouseId,
        initial_quantity: u32,
    ) -> Self {
        Self {
            id,
            product_id,
            warehouse_id,
            quantity: initial_quantity,
            reserved: 0,
            version: 0,
            last_updated: Utc::now(),
        }
    }
    
    pub fn add_stock(&mut self, amount: u32) -> Result<(), DomainError> {
        if amount == 0 {
            return Err(DomainError::ValidationError("Amount must be greater than zero".into()));
        }
        
        self.quantity += amount;
        self.last_updated = Utc::now();
        self.version += 1;
        
        Ok(())
    }
    
    pub fn remove_stock(&mut self, amount: u32) -> Result<(), DomainError> {
        if amount == 0 {
            return Err(DomainError::ValidationError("Amount must be greater than zero".into()));
        }
        
        if amount > self.available_quantity() {
            return Err(DomainError::InsufficientInventory {
                requested: amount,
                available: self.available_quantity(),
            });
        }
        
        self.quantity -= amount;
        self.last_updated = Utc::now();
        self.version += 1;
        
        Ok(())
    }
    
    pub fn reserve(&mut self, amount: u32) -> Result<(), DomainError> {
        if amount == 0 {
            return Err(DomainError::ValidationError("Amount must be greater than zero".into()));
        }
        
        if amount > self.available_quantity() {
            return Err(DomainError::InsufficientInventory {
                requested: amount,
                available: self.available_quantity(),
            });
        }
        
        self.reserved += amount;
        self.last_updated = Utc::now();
        self.version += 1;
        
        Ok(())
    }
    
    pub fn release_reservation(&mut self, amount: u32) -> Result<(), DomainError> {
        if amount == 0 {
            return Err(DomainError::ValidationError("Amount must be greater than zero".into()));
        }
        
        if amount > self.reserved {
            return Err(DomainError::ValidationError(
                format!("Cannot release more than reserved: {} > {}", amount, self.reserved)
            ));
        }
        
        self.reserved -= amount;
        self.last_updated = Utc::now();
        self.version += 1;
        
        Ok(())
    }
    
    pub fn commit_reservation(&mut self, amount: u32) -> Result<(), DomainError> {
        if amount == 0 {
            return Err(DomainError::ValidationError("Amount must be greater than zero".into()));
        }
        
        if amount > self.reserved {
            return Err(DomainError::ValidationError(
                format!("Cannot commit more than reserved: {} > {}", amount, self.reserved)
            ));
        }
        
        self.reserved -= amount;
        self.quantity -= amount;
        self.last_updated = Utc::now();
        self.version += 1;
        
        Ok(())
    }
    
    pub fn available_quantity(&self) -> u32 {
        self.quantity.saturating_sub(self.reserved)
    }
    
    // Getters
    pub fn id(&self) -> &InventoryItemId {
        &self.id
    }
    
    pub fn product_id(&self) -> &ProductId {
        &self.product_id
    }
    
    pub fn warehouse_id(&self) -> &WarehouseId {
        &self.warehouse_id
    }
    
    pub fn quantity(&self) -> u32 {
        self.quantity
    }
    
    pub fn reserved(&self) -> u32 {
        self.reserved
    }
    
    pub fn version(&self) -> u64 {
        self.version
    }
}

// src/domain/model/warehouse.rs
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WarehouseId(Uuid);

#[derive(Debug, Clone)]
pub struct Warehouse {
    id: WarehouseId,
    name: String,
    location: Location,
    status: WarehouseStatus,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WarehouseStatus {
    Active,
    Inactive,
    Maintenance,
}

#[derive(Debug, Clone)]
pub struct Location {
    address: String,
    city: String,
    state: String,
    country: String,
    postal_code: String,
    latitude: Option<f64>,
    longitude: Option<f64>,
}
```

**应用服务与并发控制**:

```rust
// src/application/inventory_service.rs
pub struct InventoryService {
    inventory_repository: Arc<dyn InventoryRepository>,
    event_publisher: Arc<dyn EventPublisher>,
}

impl InventoryService {
    pub fn new(
        inventory_repository: Arc<dyn InventoryRepository>,
        event_publisher: Arc<dyn EventPublisher>,
    ) -> Self {
        Self {
            inventory_repository,
            event_publisher,
        }
    }
    
    // 并发控制版本的库存预留
    pub async fn reserve_inventory(
        &self,
        command: ReserveInventoryCommand,
    ) -> Result<(), ApplicationError> {
        let max_retries = 3;
        let mut current_retry = 0;
        
        loop {
            // 获取库存项
            let inventory_id = InventoryItemId::from_string(&command.inventory_id)
                .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
                
            let mut inventory_item = self.inventory_repository.find_by_id(&inventory_id).await
                .map_err(ApplicationError::from)?
                .ok_or(ApplicationError::EntityNotFound(format!("Inventory item not found: {}", command.inventory_id)))?;
                
            // 记录当前版本号，用于乐观锁检查
            let current_version = inventory_item.version();
            
            // 尝试预留库存
            match inventory_item.reserve(command.quantity) {
                Ok(_) => {
                    // 尝试保存，可能会因为版本不匹配而失败
                    match self.inventory_repository.save(&inventory_item).await {
                        Ok(_) => {
                            // 发布事件
                            let event = InventoryReservedEvent {
                                inventory_id: inventory_id.to_string(),
                                product_id: inventory_item.product_id().to_string(),
                                warehouse_id: inventory_item.warehouse_id().to_string(),
                                quantity: command.quantity,
                                timestamp: Utc::now(),
                            };
                            
                            self.event_publisher.publish("inventory-events", &event).await
                                .map_err(|e| ApplicationError::EventPublishingError(e.to_string()))?;
                                
                            return Ok(());
                        },
                        Err(RepositoryError::ConcurrencyError(_)) => {
                            // 版本冲突，重试
                            current_retry += 1;
                            if current_retry >= max_retries {
                                return Err(ApplicationError::ConcurrencyError(
                                    "Maximum retries exceeded for inventory reservation".into()
                                ));
                            }
                            
                            // 添加随机延迟以减少冲突概率
                            let delay_ms = rand::thread_rng().gen_range(50..200);
                            tokio::time::sleep(Duration::from_millis(delay_ms)).await;
                            
                            continue;
                        },
                        Err(e) => return Err(ApplicationError::from(e)),
                    }
                },
                Err(e) => return Err(ApplicationError::from(e)),
            }
        }
    }
    
    // 使用分布式锁实现的库存预留
    pub async fn reserve_inventory_with_lock(
        &self,
        command: ReserveInventoryCommand,
    ) -> Result<(), ApplicationError> {
        let inventory_id = InventoryItemId::from_string(&command.inventory_id)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        // 创建锁的键
        let lock_key = format!("inventory:lock:{}", inventory_id);
        
        // 获取分布式锁
        let lock = self.lock_manager.acquire_lock(&lock_key, Duration::from_secs(10)).await
            .map_err(|e| ApplicationError::ConcurrencyError(format!("Failed to acquire lock: {}", e)))?;
            
        // 锁定成功，执行业务逻辑
        let result = async {
            let mut inventory_item = self.inventory_repository.find_by_id(&inventory_id).await
                .map_err(ApplicationError::from)?
                .ok_or(ApplicationError::EntityNotFound(
                    format!("Inventory item not found: {}", command.inventory_id)
                ))?;
                
            // 预留库存
            inventory_item.reserve(command.quantity)
                .map_err(ApplicationError::from)?;
                
            // 保存
            self.inventory_repository.save(&inventory_item).await
                .map_err(ApplicationError::from)?;
                
            // 发布事件
            let event = InventoryReservedEvent {
                inventory_id: inventory_id.to_string(),
                product_id: inventory_item.product_id().to_string(),
                warehouse_id: inventory_item.warehouse_id().to_string(),
                quantity: command.quantity,
                timestamp: Utc::now(),
            };
            
            self.event_publisher.publish("inventory-events", &event).await
                .map_err(|e| ApplicationError::EventPublishingError(e.to_string()))?;
                
            Ok(())
        }.await;
        
        // 释放锁
        if let Err(e) = lock.release().await {
            tracing::warn!("Failed to release lock: {}", e);
        }
        
        result
    }
    
    // 其他库存服务方法...
}
```

**存储层与乐观并发控制**:

```rust
// src/infrastructure/persistence/postgres/inventory_repository.rs
pub struct PostgresInventoryRepository {
    pool: PgPool,
}

impl PostgresInventoryRepository {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
}

#[async_trait]
impl InventoryRepository for PostgresInventoryRepository {
    async fn save(&self, item: &InventoryItem) -> Result<(), RepositoryError> {
        // 使用乐观锁进行并发控制
        let current_version = item.version() - 1; // 当前数据库中的版本
        
        let result = sqlx::query!(
            r#"
            UPDATE inventory_items 
            SET quantity = $1, 
                reserved = $2, 
                version = $3, 
                last_updated = $4
            WHERE id = $5 AND version = $6
            "#,
            item.quantity() as i32,
            item.reserved() as i32,
            item.version() as i64,
            item.last_updated(),
            item.id().to_string(),
            current_version as i64,
        )
        .execute(&self.pool)
        .await
        .map_err(|e| RepositoryError::QueryError(e.to_string()))?;
        
        // 检查是否有行被更新
        if result.rows_affected() == 0 {
            // 没有行被更新，可能是版本不匹配
            // 检查记录是否存在
            let exists = sqlx::query!(
                "SELECT 1 FROM inventory_items WHERE id = $1",
                item.id().to_string()
            )
            .fetch_optional(&self.pool)
            .await
            .map_err(|e| RepositoryError::QueryError(e.to_string()))?
            .is_some();
            
            if exists {
                // 记录存在但版本不匹配，是并发冲突
                return Err(RepositoryError::ConcurrencyError(
                    format!("Optimistic concurrency control failed for inventory item: {}", item.id())
                ));
            } else {
                // 记录不存在，执行插入
                sqlx::query!(
                    r#"
                    INSERT INTO inventory_items (
                        id, product_id, warehouse_id, 
                        quantity, reserved, version, 
                        last_updated
                    ) VALUES ($1, $2, $3, $4, $5, $6, $7)
                    "#,
                    item.id().to_string(),
                    item.product_id().to_string(),
                    item.warehouse_id().to_string(),
                    item.quantity() as i32,
                    item.reserved() as i32,
                    item.version() as i64,
                    item.last_updated(),
                )
                .execute(&self.pool)
                .await
                .map_err(|e| RepositoryError::QueryError(e.to_string()))?;
            }
        }
        
        Ok(())
    }
    
    async fn find_by_id(&self, id: &InventoryItemId) -> Result<Option<InventoryItem>, RepositoryError> {
        // 实现从数据库查询并映射到领域对象的逻辑
        let row = sqlx::query!(
            r#"
            SELECT 
                id, product_id, warehouse_id, 
                quantity, reserved, version, 
                last_updated
            FROM inventory_items
            WHERE id = $1
            "#,
            id.to_string()
        )
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| RepositoryError::QueryError(e.to_string()))?;
        
        match row {
            Some(row) => {
                // 映射到领域对象
                let inventory_id = InventoryItemId::from_string(&row.id)
                    .map_err(|e| RepositoryError::DataError(e.to_string()))?;
                    
                let product_id = ProductId::from_string(&row.product_id)
                    .map_err(|e| RepositoryError::DataError(e.to_string()))?;
                    
                let warehouse_id = WarehouseId::from_string(&row.warehouse_id)
                    .map_err(|e| RepositoryError::DataError(e.to_string()))?;
                    
                let item = InventoryItem::from_persistence(
                    inventory_id,
                    product_id,
                    warehouse_id,
                    row.quantity as u32,
                    row.reserved as u32,
                    row.version as u64,
                    row.last_updated,
                );
                
                Ok(Some(item))
            },
            None => Ok(None),
        }
    }
}
```

**分布式锁实现**:

```rust
// src/infrastructure/lock/redis_lock_manager.rs
pub struct RedisLockManager {
    client: redis::Client,
}

impl RedisLockManager {
    pub fn new(redis_url: &str) -> Result<Self, redis::RedisError> {
        let client = redis::Client::open(redis_url)?;
        Ok(Self { client })
    }
    
    pub async fn acquire_lock(&self, key: &str, ttl: Duration) -> Result<RedisLock, LockError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| LockError::ConnectionError(e.to_string()))?;
            
        // 生成唯一值作为锁的标识
        let lock_value = format!("{}", Uuid::new_v4());
        
        // 尝试获取锁，使用NX选项确保只有在键不存在时才设置
        let result: bool = redis::cmd("SET")
            .arg(key)
            .arg(&lock_value)
            .arg("NX")  // 仅在键不存在时设置
            .arg("PX")  // 过期时间单位为毫秒
            .arg(ttl.as_millis() as u64)
            .query_async(&mut conn)
            .await
            .map_err(|e| LockError::OperationError(e.to_string()))?;
            
        if result {
            // 成功获取锁
            Ok(RedisLock {
                client: self.client.clone(),
                key: key.to_string(),
                value: lock_value,
            })
        } else {
            // 获取锁失败
            Err(LockError::AcquisitionFailed(format!("Failed to acquire lock for key: {}", key)))
        }
    }
}

pub struct RedisLock {
    client: redis::Client,
    key: String,
    value: String,
}

impl RedisLock {
    pub async fn release(&self) -> Result<(), LockError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| LockError::ConnectionError(e.to_string()))?;
            
        // 使用Lua脚本确保原子性，只释放我们持有的锁
        let script = r#"
        if redis.call("GET", KEYS[1]) == ARGV[1] then
            return redis.call("DEL", KEYS[1])
        else
            return 0
        end
        "#;
        
        let result: i32 = redis::Script::new(script)
            .key(&self.key)
            .arg(&self.value)
            .invoke_async(&mut conn)
            .await
            .map_err(|e| LockError::OperationError(e.to_string()))?;
            
        if result == 1 {
            Ok(())
        } else {
            Err(LockError::ReleaseFailed(format!("Failed to release lock for key: {}", self.key)))
        }
    }
}
```

**实时通知系统**:

```rust
// src/infrastructure/notification/websocket_server.rs
pub struct InventoryWebSocketServer {
    inventory_service: Arc<InventoryService>,
    clients: Arc<RwLock<HashMap<String, mpsc::UnboundedSender<Message>>>>,
}

impl InventoryWebSocketServer {
    pub fn new(inventory_service: Arc<InventoryService>) -> Self {
        Self {
            inventory_service,
            clients: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub async fn handle_connection(&self, websocket: WebSocket, client_id: String) {
        // 将连接分为发送和接收部分
        let (ws_sender, mut ws_receiver) = websocket.split();
        
        // 创建通道，用于向 WebSocket 发送消息
        let (tx, rx) = mpsc::unbounded_channel();
        let rx = UnboundedReceiverStream::new(rx);
        
        // 将接收器连接到 WebSocket 发送器
        tokio::task::spawn(rx.forward(ws_sender).map(|result| {
            if let Err(e) = result {
                tracing::error!("WebSocket send error: {}", e);
            }
        }));
        
        // 将发送器保存到客户端映射中
        {
            let mut clients = self.clients.write().await;
            clients.insert(client_id.clone(), tx);
        }
        
        // 处理接收到的 WebSocket 消息
        while let Some(result) = ws_receiver.next().await {
            match result {
                Ok(msg) => {
                    self.handle_message(msg, &client_id).await;
                }
                Err(e) => {
                    tracing::error!("WebSocket error: {}", e);
                    break;
                }
            }
        }
        
        // 连接关闭，移除客户端
        {
            let mut clients = self.clients.write().await;
            clients.remove(&client_id);
        }
        
        tracing::info!("Client disconnected: {}", client_id);
    }
    
    async fn handle_message(&self, msg: Message, client_id: &str) {
        if let Ok(text) = msg.to_str() {
            // 解析客户端消息
            if let Ok(request) = serde_json::from_str::<InventorySubscriptionRequest>(text) {
                match request.action.as_str() {
                    "subscribe" => {
                        // 处理订阅请求
                        for product_id in &request.product_ids {
                            self.subscribe_to_product(client_id, product_id).await;
                        }
                    }
                    "unsubscribe" => {
                        // 处理取消订阅请求
                        for product_id in &request.product_ids {
                            self.unsubscribe_from_product(client_id, product_id).await;
                        }
                    }
                    _ => {
                        tracing::warn!("Unknown action: {}", request.action);
                    }
                }
            } else {
                tracing::warn!("Invalid message format: {}", text);
            }
        }
    }
    
    async fn subscribe_to_product(&self, client_id: &str, product_id: &str) {
        // 在实际实现中，这里会将客户端ID与产品ID关联起来，
        // 以便在产品库存变化时通知相关客户端
        
        // 获取最新的库存状态并发送给客户端
        match self.inventory_service.get_product_inventory(product_id).await {
            Ok(Some(inventory)) => {
                let update = InventoryUpdate {
                    product_id: product_id.to_string(),
                    quantity: inventory.available_quantity(),
                    timestamp: Utc::now(),
                };
                
                self.send_to_client(client_id, &update).await;
            }
            _ => {
                tracing::warn!("Product not found or error: {}", product_id);
            }
        }
    }
    
    async fn unsubscribe_from_product(&self, client_id: &str, product_id: &str) {
        // 解除客户端与产品的订阅关系
    }
    
    pub async fn broadcast_inventory_update(&self, update: &InventoryUpdate) {
        // 向订阅了特定产品的客户端广播更新
        let json = serde_json::to_string(update).unwrap_or_default();
        let message = Message::Text(json);
        
        let clients = self.clients.read().await;
        for (_, tx) in clients.iter() {
            if let Err(e) = tx.send(message.clone()) {
                tracing::error!("Failed to send message: {}", e);
            }
        }
    }
    
    async fn send_to_client(&self, client_id: &str, update: &InventoryUpdate) {
        let clients = self.clients.read().await;
        if let Some(tx) = clients.get(client_id) {
            let json = serde_json::to_string(update).unwrap_or_default();
            let message = Message::Text(json);
            
            if let Err(e) = tx.send(message) {
                tracing::error!("Failed to send message to client {}: {}", client_id, e);
            }
        }
    }
}
```

**基于Redis的发布订阅机制**:

```rust
// src/infrastructure/notification/redis_pubsub.rs
pub struct RedisInventoryNotifier {
    publisher: redis::Client,
    channel: String,
}

impl RedisInventoryNotifier {
    pub fn new(redis_url: &str, channel: &str) -> Result<Self, redis::RedisError> {
        let publisher = redis::Client::open(redis_url)?;
        
        Ok(Self {
            publisher,
            channel: channel.to_string(),
        })
    }
    
    pub async fn publish_inventory_update(&self, update: &InventoryUpdate) -> Result<(), NotificationError> {
        let mut conn = self.publisher.get_async_connection().await
            .map_err(|e| NotificationError::ConnectionError(e.to_string()))?;
            
        let json = serde_json::to_string(update)
            .map_err(|e| NotificationError::SerializationError(e.to_string()))?;
            
        // 发布到Redis通道
        let _: () = redis::cmd("PUBLISH")
            .arg(&self.channel)
            .arg(json)
            .query_async(&mut conn)
            .await
            .map_err(|e| NotificationError::PublishError(e.to_string()))?;
            
        Ok(())
    }
    
    pub async fn subscribe_and_process<F>(
        redis_url: &str,
        channel: &str,
        mut callback: F,
    ) -> Result<(), NotificationError>
    where
        F: FnMut(InventoryUpdate) -> Result<(), NotificationError> + Send + 'static,
    {
        let client = redis::Client::open(redis_url)
            .map_err(|e| NotificationError::ConnectionError(e.to_string()))?;
            
        let mut pubsub = client.get_async_connection().await
            .map_err(|e| NotificationError::ConnectionError(e.to_string()))?
            .into_pubsub();
            
        pubsub.subscribe(channel).await
            .map_err(|e| NotificationError::SubscriptionError(e.to_string()))?;
            
        let mut stream = pubsub.on_message();
        
        tokio::spawn(async move {
            while let Some(msg) = stream.next().await {
                let payload: String = msg.get_payload()
                    .unwrap_or_else(|e| {
                        tracing::error!("Failed to get message payload: {}", e);
                        String::new()
                    });
                    
                if !payload.is_empty() {
                    match serde_json::from_str::<InventoryUpdate>(&payload) {
                        Ok(update) => {
                            if let Err(e) = callback(update) {
                                tracing::error!("Error processing inventory update: {}", e);
                            }
                        },
                        Err(e) => {
                            tracing::error!("Failed to deserialize inventory update: {}", e);
                        }
                    }
                }
            }
        });
        
        Ok(())
    }
}
```

### 事件驱动微服务架构

以下是一个事件驱动的微服务架构示例，展示如何在Rust中设计事件驱动系统：

**领域事件定义**:

```rust
// src/domain/event/mod.rs
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum DomainEvent {
    OrderCreated(OrderCreatedEvent),
    OrderItemAdded(OrderItemAddedEvent),
    OrderSubmitted(OrderSubmittedEvent),
    OrderPaid(OrderPaidEvent),
    OrderShipped(OrderShippedEvent),
    OrderCancelled(OrderCancelledEvent),
    
    ProductCreated(ProductCreatedEvent),
    ProductPriceUpdated(ProductPriceUpdatedEvent),
    ProductStockChanged(ProductStockChangedEvent),
    
    PaymentProcessed(PaymentProcessedEvent),
    PaymentFailed(PaymentFailedEvent),
    
    InventoryReserved(InventoryReservedEvent),
    InventoryReleased(InventoryReleasedEvent),
    InventoryCommitted(InventoryCommittedEvent),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderCreatedEvent {
    pub order_id: String,
    pub customer_id: String,
    pub timestamp: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderItemAddedEvent {
    pub order_id: String,
    pub product_id: String,
    pub product_name: String,
    pub quantity: u32,
    pub unit_price: f64,
    pub timestamp: DateTime<Utc>,
}

// 其他事件结构体...
```

**事件发布者**:

```rust
// src/infrastructure/messaging/kafka_event_publisher.rs
pub struct KafkaEventPublisher {
    producer: FutureProducer,
}

impl KafkaEventPublisher {
    pub fn new(bootstrap_servers: &str) -> Result<Self, rdkafka::error::KafkaError> {
        let producer: FutureProducer = ClientConfig::new()
            .set("bootstrap.servers", bootstrap_servers)
            .set("message.timeout.ms", "5000")
            .create()?;
            
        Ok(Self { producer })
    }
}

#[async_trait]
impl EventPublisher for KafkaEventPublisher {
    async fn publish<T: Serialize + Send + Sync>(
        &self,
        topic: &str,
        event: &T,
    ) -> Result<(), PublishError> {
        let payload = serde_json::to_string(event)
            .map_err(|e| PublishError::SerializationError(e.to_string()))?;
            
        // 生成事件键（用于分区）
        let key = match event {
            // 根据事件类型确定合适的键
            event if topic == "order-events" => {
                if let Ok(order_event) = serde_json::from_value::<OrderEvent>(serde_json::to_value(event).unwrap()) {
                    match order_event {
                        OrderEvent::OrderCreated { order_id, .. } => order_id,
                        OrderEvent::OrderItemAdded { order_id, .. } => order_id,
                        // 其他订单事件类型...
                        _ => Uuid::new_v4().to_string(),
                    }
                } else {
                    Uuid::new_v4().to_string()
                }
            },
            // 其他主题的键生成逻辑...
            _ => Uuid::new_v4().to_string(),
        };
        
        // 发送消息
        self.producer.send(
            FutureRecord::to(topic)
                .payload(&payload)
                .key(&key),
            Duration::from_secs(5),
        )
        .await
        .map_err(|(e, _)| PublishError::PublishError(e.to_string()))?;
            
        Ok(())
    }
}
```

**事件消费者**:

```rust
// src/infrastructure/messaging/kafka_event_consumer.rs
pub struct KafkaEventConsumer {
    consumer: StreamConsumer,
}

impl KafkaEventConsumer {
    pub fn new(
        bootstrap_servers: &str,
        group_id: &str,
        topics: &[&str],
    ) -> Result<Self, rdkafka::error::KafkaError> {
        let consumer: StreamConsumer = ClientConfig::new()
            .set("bootstrap.servers", bootstrap_servers)
            .set("group.id", group_id)
            .set("enable.auto.commit", "true")
            .set("auto.offset.reset", "earliest")
            .create()?;
            
        consumer.subscribe(topics)?;
        
        Ok(Self { consumer })
    }
    
    pub async fn start<F, Fut>(&self, mut handler: F) -> Result<(), ConsumerError>
    where
        F: FnMut(DomainEvent, Option<String>) -> Fut + Send,
        Fut: Future<Output = Result<(), ConsumerError>> + Send,
    {
        let mut message_stream = self.consumer.stream();
        
        while let Some(message) = message_stream.next().await {
            match message {
                Ok(msg) => {
                    let payload = match msg.payload() {
                        Some(data) => data,
                        None => {
                            tracing::warn!("Empty message payload");
                            continue;
                        }
                    };
                    
                    let key = msg.key().map(|k| 
                        std::str::from_utf8(k)
                            .unwrap_or_default()
                            .to_string()
                    );
                    
                    match serde_json::from_slice::<DomainEvent>(payload) {
                        Ok(event) => {
                            if let Err(e) = handler(event, key).await {
                                tracing::error!("Error handling event: {}", e);
                            }
                        },
                        Err(e) => {
                            tracing::error!("Failed to deserialize event: {}", e);
                        }
                    }
                },
                Err(e) => {
                    tracing::error!("Kafka error: {}", e);
                }
            }
        }
        
        Ok(())
    }
}
```

**订单服务中的事件处理**:

```rust
// src/application/order_event_handlers.rs
pub struct OrderEventHandlers {
    order_service: Arc<OrderService>,
    inventory_service_client: Arc<InventoryServiceClient>,
    payment_service_client: Arc<PaymentServiceClient>,
}

impl OrderEventHandlers {
    pub fn new(
        order_service: Arc<OrderService>,
        inventory_service_client: Arc<InventoryServiceClient>,
        payment_service_client: Arc<PaymentServiceClient>,
    ) -> Self {
        Self {
            order_service,
            inventory_service_client,
            payment_service_client,
        }
    }
    
    pub async fn handle_event(&self, event: DomainEvent) -> Result<(), ApplicationError> {
        match event {
            DomainEvent::OrderSubmitted(event) => {
                self.handle_order_submitted(event).await
            },
            DomainEvent::PaymentProcessed(event) => {
                self.handle_payment_processed(event).await
            },
            DomainEvent::PaymentFailed(event) => {
                self.handle_payment_failed(event).await
            },
            DomainEvent::InventoryCommitted(event) => {
                self.handle_inventory_committed(event).await
            },
            // 处理其他相关事件...
            _ => Ok(()),
        }
    }
    
    async fn handle_order_submitted(&self, event: OrderSubmittedEvent) -> Result<(), ApplicationError> {
        // 1. 获取订单
        let order_id = OrderId::from_string(&event.order_id)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        let order = self.order_service.get_order(&order_id).await?
            .ok_or(ApplicationError::EntityNotFound(format!("Order not found: {}", event.order_id)))?;
            
        // 2. 请求预留库存
        let reserve_result = self.inventory_service_client.reserve_inventory(&order).await;
        
        match reserve_result {
            Ok(_) => {
                // 3. 处理支付
                self.payment_service_client.process_payment(&order).await
                    .map_err(|e| ApplicationError::ExternalServiceError(format!("

```rust
                self.payment_service_client.process_payment(&order).await
                    .map_err(|e| ApplicationError::ExternalServiceError(format!("Payment processing failed: {}", e)))
            },
            Err(e) => {
                // 库存预留失败，更新订单状态
                self.order_service.mark_order_failed(
                    &order_id, 
                    &format!("Failed to reserve inventory: {}", e)
                ).await?;
                
                Err(ApplicationError::ExternalServiceError(format!("Inventory reservation failed: {}", e)))
            }
        }
    }
    
    async fn handle_payment_processed(&self, event: PaymentProcessedEvent) -> Result<(), ApplicationError> {
        // 1. 获取订单ID
        let order_id = OrderId::from_string(&event.order_id)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        // 2. 更新订单状态为已支付
        self.order_service.mark_order_paid(&order_id, &event.transaction_id).await?;
        
        // 3. 请求确认库存（从预留状态转为已消费）
        let order = self.order_service.get_order(&order_id).await?
            .ok_or(ApplicationError::EntityNotFound(format!("Order not found: {}", event.order_id)))?;
            
        self.inventory_service_client.commit_inventory(&order).await
            .map_err(|e| ApplicationError::ExternalServiceError(format!("Inventory commit failed: {}", e)))?;
            
        Ok(())
    }
    
    async fn handle_payment_failed(&self, event: PaymentFailedEvent) -> Result<(), ApplicationError> {
        // 1. 获取订单ID
        let order_id = OrderId::from_string(&event.order_id)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        // 2. 更新订单状态为支付失败
        self.order_service.mark_order_payment_failed(
            &order_id, 
            &event.error_message
        ).await?;
        
        // 3. 释放预留的库存
        let order = self.order_service.get_order(&order_id).await?
            .ok_or(ApplicationError::EntityNotFound(format!("Order not found: {}", event.order_id)))?;
            
        self.inventory_service_client.release_inventory(&order).await
            .map_err(|e| ApplicationError::ExternalServiceError(format!("Inventory release failed: {}", e)))?;
            
        Ok(())
    }
    
    async fn handle_inventory_committed(&self, event: InventoryCommittedEvent) -> Result<(), ApplicationError> {
        // 1. 获取订单ID
        let order_id = OrderId::from_string(&event.order_id)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        // 2. 更新订单状态为处理中
        self.order_service.mark_order_processing(&order_id).await?;
        
        // 3. 初始化物流流程
        // 在实际应用中，这里可能会调用物流服务API或发布物流相关事件
        
        Ok(())
    }
}
```

**库存服务中的事件处理**:

```rust
// src/application/inventory_event_handlers.rs
pub struct InventoryEventHandlers {
    inventory_service: Arc<InventoryService>,
    event_publisher: Arc<dyn EventPublisher>,
}

impl InventoryEventHandlers {
    pub fn new(
        inventory_service: Arc<InventoryService>,
        event_publisher: Arc<dyn EventPublisher>,
    ) -> Self {
        Self {
            inventory_service,
            event_publisher,
        }
    }
    
    pub async fn handle_event(&self, event: DomainEvent) -> Result<(), ApplicationError> {
        match event {
            DomainEvent::InventoryReserved(event) => {
                self.handle_inventory_reserved(event).await
            },
            DomainEvent::OrderCancelled(event) => {
                self.handle_order_cancelled(event).await
            },
            DomainEvent::ProductStockChanged(event) => {
                self.handle_product_stock_changed(event).await
            },
            // 处理其他相关事件...
            _ => Ok(()),
        }
    }
    
    async fn handle_inventory_reserved(&self, event: InventoryReservedEvent) -> Result<(), ApplicationError> {
        // 记录库存预留事件（可用于审计或报告）
        tracing::info!(
            order_id = %event.order_id,
            product_id = %event.product_id,
            quantity = %event.quantity,
            "Inventory successfully reserved"
        );
        
        // 发布库存状态更新事件（用于其他服务可能需要了解库存状态）
        let stock_event = ProductStockChangedEvent {
            product_id: event.product_id.clone(),
            warehouse_id: event.warehouse_id.clone(),
            new_available_quantity: event.remaining_quantity,
            change_type: "reserved".to_string(),
            change_amount: event.quantity,
            timestamp: Utc::now(),
        };
        
        self.event_publisher.publish("inventory-events", &stock_event).await
            .map_err(|e| ApplicationError::EventPublishingError(e.to_string()))?;
            
        Ok(())
    }
    
    async fn handle_order_cancelled(&self, event: OrderCancelledEvent) -> Result<(), ApplicationError> {
        // 获取订单详情，释放预留的库存
        let order_id = OrderId::from_string(&event.order_id)
            .map_err(|e| ApplicationError::ValidationError(e.to_string()))?;
            
        // 获取订单中的预留库存信息
        let reserved_items = self.inventory_service.get_reserved_items_for_order(&order_id).await?;
        
        // 释放每个预留项
        for item in reserved_items {
            let command = ReleaseInventoryCommand {
                inventory_id: item.inventory_id.to_string(),
                order_id: order_id.to_string(),
                product_id: item.product_id.to_string(),
                quantity: item.quantity,
            };
            
            self.inventory_service.release_inventory(command).await?;
        }
        
        tracing::info!(
            order_id = %event.order_id,
            "Released inventory for cancelled order"
        );
        
        Ok(())
    }
    
    async fn handle_product_stock_changed(&self, event: ProductStockChangedEvent) -> Result<(), ApplicationError> {
        // 更新实时库存缓存或通知订阅系统
        // 这可能涉及更新缓存、发送WebSocket通知等
        
        // 例如，向所有关注该产品的客户端发送实时更新
        let inventory_update = InventoryUpdate {
            product_id: event.product_id.clone(),
            warehouse_id: event.warehouse_id.clone(),
            available_quantity: event.new_available_quantity,
            timestamp: event.timestamp,
        };
        
        // 如果存在实时通知组件，调用它
        if let Some(notifier) = &self.real_time_notifier {
            notifier.notify_inventory_change(&inventory_update).await
                .map_err(|e| ApplicationError::NotificationError(e.to_string()))?;
        }
        
        Ok(())
    }
}
```

**微服务通信客户端**:

```rust
// src/infrastructure/client/inventory_service_client.rs
pub struct InventoryServiceClient {
    client: tonic::transport::Channel,
}

impl InventoryServiceClient {
    pub async fn new(address: &str) -> Result<Self, tonic::transport::Error> {
        let channel = tonic::transport::Channel::from_shared(address.to_string())?
            .connect()
            .await?;
            
        Ok(Self { client: channel })
    }
    
    pub async fn reserve_inventory(&self, order: &Order) -> Result<(), ServiceError> {
        // 创建gRPC客户端
        let mut client = inventory_proto::inventory_client::InventoryClient::new(self.client.clone());
        
        // 构建请求
        let mut items = Vec::new();
        for item in order.items() {
            items.push(inventory_proto::ReservationItem {
                product_id: item.product_id().to_string(),
                quantity: item.quantity() as u32,
            });
        }
        
        let request = tonic::Request::new(inventory_proto::ReserveInventoryRequest {
            order_id: order.id().to_string(),
            items,
        });
        
        // 发送请求
        match client.reserve_inventory(request).await {
            Ok(_) => Ok(()),
            Err(status) => Err(ServiceError::InventoryServiceError(
                format!("Failed to reserve inventory: {}", status)
            )),
        }
    }
    
    pub async fn commit_inventory(&self, order: &Order) -> Result<(), ServiceError> {
        // 创建gRPC客户端
        let mut client = inventory_proto::inventory_client::InventoryClient::new(self.client.clone());
        
        // 构建请求
        let request = tonic::Request::new(inventory_proto::CommitInventoryRequest {
            order_id: order.id().to_string(),
        });
        
        // 发送请求
        match client.commit_inventory(request).await {
            Ok(_) => Ok(()),
            Err(status) => Err(ServiceError::InventoryServiceError(
                format!("Failed to commit inventory: {}", status)
            )),
        }
    }
    
    pub async fn release_inventory(&self, order: &Order) -> Result<(), ServiceError> {
        // 创建gRPC客户端
        let mut client = inventory_proto::inventory_client::InventoryClient::new(self.client.clone());
        
        // 构建请求
        let request = tonic::Request::new(inventory_proto::ReleaseInventoryRequest {
            order_id: order.id().to_string(),
        });
        
        // 发送请求
        match client.release_inventory(request).await {
            Ok(_) => Ok(()),
            Err(status) => Err(ServiceError::InventoryServiceError(
                format!("Failed to release inventory: {}", status)
            )),
        }
    }
}

// src/infrastructure/client/payment_service_client.rs
pub struct PaymentServiceClient {
    client: tonic::transport::Channel,
}

impl PaymentServiceClient {
    pub async fn new(address: &str) -> Result<Self, tonic::transport::Error> {
        let channel = tonic::transport::Channel::from_shared(address.to_string())?
            .connect()
            .await?;
            
        Ok(Self { client: channel })
    }
    
    pub async fn process_payment(&self, order: &Order) -> Result<(), ServiceError> {
        // 创建gRPC客户端
        let mut client = payment_proto::payment_client::PaymentClient::new(self.client.clone());
        
        // 构建请求
        let request = tonic::Request::new(payment_proto::ProcessPaymentRequest {
            order_id: order.id().to_string(),
            customer_id: order.customer_id().to_string(),
            amount: order.total_amount().value(),
            currency: order.total_amount().currency().to_string(),
        });
        
        // 发送请求
        match client.process_payment(request).await {
            Ok(_) => Ok(()),
            Err(status) => Err(ServiceError::PaymentServiceError(
                format!("Failed to process payment: {}", status)
            )),
        }
    }
}
```

**API 网关实现**:

```rust
// src/interfaces/api_gateway/mod.rs
pub struct ApiGateway {
    order_service: Arc<OrderService>,
    product_service: Arc<ProductService>,
    payment_service: Arc<PaymentService>,
    auth_service: Arc<AuthService>,
}

impl ApiGateway {
    pub fn new(
        order_service: Arc<OrderService>,
        product_service: Arc<ProductService>,
        payment_service: Arc<PaymentService>,
        auth_service: Arc<AuthService>,
    ) -> Self {
        Self {
            order_service,
            product_service,
            payment_service,
            auth_service,
        }
    }
    
    // API 路由配置
    pub fn configure_routes(cfg: &mut web::ServiceConfig) {
        cfg.service(
            web::scope("/api")
                // 产品API
                .service(
                    web::scope("/products")
                        .route("", web::get().to(Self::get_products))
                        .route("/{id}", web::get().to(Self::get_product))
                )
                // 订单API
                .service(
                    web::scope("/orders")
                        .route("", web::post().to(Self::create_order))
                        .route("", web::get().to(Self::get_orders))
                        .route("/{id}", web::get().to(Self::get_order))
                        .route("/{id}/items", web::post().to(Self::add_order_item))
                        .route("/{id}/submit", web::post().to(Self::submit_order))
                )
                // 支付API
                .service(
                    web::scope("/payments")
                        .route("/webhook", web::post().to(Self::payment_webhook))
                )
                // 用户API
                .service(
                    web::scope("/users")
                        .route("/register", web::post().to(Self::register_user))
                        .route("/login", web::post().to(Self::login))
                )
        );
    }
    
    // 实现API endpoint处理函数
    
    async fn get_products(
        data: web::Data<Arc<Self>>,
        query: web::Query<ProductQuery>,
    ) -> Result<HttpResponse, Error> {
        // 调用产品服务获取产品列表
        let products = data.product_service.find_products(
            query.category.clone(),
            query.min_price,
            query.max_price,
            query.page.unwrap_or(1),
            query.page_size.unwrap_or(20),
        ).await
        .map_err(|e| {
            tracing::error!("Error fetching products: {}", e);
            HttpResponse::InternalServerError().json(ErrorResponse {
                error: "Failed to fetch products".into(),
                message: e.to_string(),
            })
        })?;
        
        Ok(HttpResponse::Ok().json(products))
    }
    
    async fn get_product(
        data: web::Data<Arc<Self>>,
        path: web::Path<String>,
    ) -> Result<HttpResponse, Error> {
        let product_id = path.into_inner();
        
        // 调用产品服务获取单个产品
        let product = data.product_service.get_product_by_id(&product_id).await
            .map_err(|e| {
                tracing::error!("Error fetching product {}: {}", product_id, e);
                HttpResponse::InternalServerError().json(ErrorResponse {
                    error: "Failed to fetch product".into(),
                    message: e.to_string(),
                })
            })?;
            
        match product {
            Some(p) => Ok(HttpResponse::Ok().json(p)),
            None => Ok(HttpResponse::NotFound().json(ErrorResponse {
                error: "Product not found".into(),
                message: format!("Product with ID {} does not exist", product_id),
            })),
        }
    }
    
    async fn create_order(
        data: web::Data<Arc<Self>>,
        jwt: JwtToken,
        body: web::Json<CreateOrderRequest>,
    ) -> Result<HttpResponse, Error> {
        // 验证JWT令牌
        let claims = data.auth_service.validate_token(&jwt.0)
            .map_err(|e| {
                HttpResponse::Unauthorized().json(ErrorResponse {
                    error: "Invalid authentication".into(),
                    message: e.to_string(),
                })
            })?;
            
        // 创建订单命令
        let command = CreateOrderCommand {
            customer_id: claims.sub, // 从JWT中获取客户ID
            shipping_address: body.shipping_address.clone(),
        };
        
        // 调用订单服务创建订单
        let order_id = data.order_service.create_order(command).await
            .map_err(|e| {
                tracing::error!("Error creating order: {}", e);
                HttpResponse::InternalServerError().json(ErrorResponse {
                    error: "Failed to create order".into(),
                    message: e.to_string(),
                })
            })?;
            
        Ok(HttpResponse::Created().json(CreateOrderResponse {
            order_id: order_id.to_string(),
            message: "Order created successfully".into(),
        }))
    }
    
    // 其他API endpoint处理函数...
}
```

**服务注册与发现**:

```rust
// src/infrastructure/discovery/consul_service_registry.rs
pub struct ConsulServiceRegistry {
    client: reqwest::Client,
    consul_url: String,
    service_id: String,
    service_name: String,
    service_address: String,
    service_port: u16,
    health_check_interval: Duration,
}

impl ConsulServiceRegistry {
    pub fn new(
        consul_url: String,
        service_id: String,
        service_name: String,
        service_address: String,
        service_port: u16,
        health_check_interval: Duration,
    ) -> Self {
        Self {
            client: reqwest::Client::new(),
            consul_url,
            service_id,
            service_name,
            service_address,
            service_port,
            health_check_interval,
        }
    }
    
    pub async fn register(&self) -> Result<(), DiscoveryError> {
        let register_url = format!("{}/v1/agent/service/register", self.consul_url);
        
        // 构建注册请求
        let registration = json!({
            "ID": self.service_id,
            "Name": self.service_name,
            "Address": self.service_address,
            "Port": self.service_port,
            "Check": {
                "HTTP": format!("http://{}:{}/health", self.service_address, self.service_port),
                "Interval": format!("{}s", self.health_check_interval.as_secs()),
                "Timeout": "5s",
                "DeregisterCriticalServiceAfter": "1m"
            },
            "Tags": ["rust", &self.service_name]
        });
        
        // 发送注册请求
        let response = self.client.put(&register_url)
            .json(&registration)
            .send()
            .await
            .map_err(|e| DiscoveryError::RegistrationError(e.to_string()))?;
            
        if !response.status().is_success() {
            let error_text = response.text().await
                .unwrap_or_else(|_| "Unknown error".to_string());
                
            return Err(DiscoveryError::RegistrationError(format!(
                "Failed to register service: {}", error_text
            )));
        }
        
        tracing::info!("Service registered successfully with Consul");
        Ok(())
    }
    
    pub async fn deregister(&self) -> Result<(), DiscoveryError> {
        let deregister_url = format!("{}/v1/agent/service/deregister/{}", self.consul_url, self.service_id);
        
        // 发送注销请求
        let response = self.client.put(&deregister_url)
            .send()
            .await
            .map_err(|e| DiscoveryError::DeregistrationError(e.to_string()))?;
            
        if !response.status().is_success() {
            let error_text = response.text().await
                .unwrap_or_else(|_| "Unknown error".to_string());
                
            return Err(DiscoveryError::DeregistrationError(format!(
                "Failed to deregister service: {}", error_text
            )));
        }
        
        tracing::info!("Service deregistered successfully from Consul");
        Ok(())
    }
    
    pub async fn discover_service(&self, service_name: &str) -> Result<Vec<ServiceEndpoint>, DiscoveryError> {
        let discover_url = format!("{}/v1/health/service/{}", self.consul_url, service_name);
        
        // 发送服务发现请求
        let response = self.client.get(&discover_url)
            .query(&[("passing", "true")])  // 只返回健康检查通过的服务
            .send()
            .await
            .map_err(|e| DiscoveryError::DiscoveryError(e.to_string()))?;
            
        if !response.status().is_success() {
            let error_text = response.text().await
                .unwrap_or_else(|_| "Unknown error".to_string());
                
            return Err(DiscoveryError::DiscoveryError(format!(
                "Failed to discover service: {}", error_text
            )));
        }
        
        // 解析响应
        let services: Vec<ConsulService> = response.json().await
            .map_err(|e| DiscoveryError::ResponseParsingError(e.to_string()))?;
            
        // 转换为服务端点列表
        let endpoints = services.into_iter()
            .map(|service| {
                ServiceEndpoint {
                    id: service.Service.ID,
                    address: service.Service.Address,
                    port: service.Service.Port,
                }
            })
            .collect();
            
        Ok(endpoints)
    }
}

#[derive(Debug, Deserialize)]
struct ConsulService {
    Service: ConsulServiceDetails,
}

#[derive(Debug, Deserialize)]
struct ConsulServiceDetails {
    ID: String,
    Address: String,
    Port: u16,
}
```

## 9. 工程化最佳实践

### 测试策略

以下是针对不同层次的测试策略示例：

**单元测试示例**:

```rust
// src/domain/model/product_tests.rs
#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::model::money::Money;
    use crate::domain::model::product::{Product, ProductId, ProductStatus};
    
    #[test]
    fn test_create_product_with_valid_data() {
        // Arrange
        let id = ProductId::new();
        let name = "Test Product".to_string();
        let description = "A test product".to_string();
        let price = Money::new(29.99, Currency::USD).unwrap();
        let initial_quantity = 100;
        
        // Act
        let product = Product::new(
            id.clone(),
            name.clone(),
            description.clone(),
            price.clone(),
            initial_quantity,
            CategoryId::new(),
        );
        
        // Assert
        assert!(product.is_ok());
        let product = product.unwrap();
        assert_eq!(product.id(), &id);
        assert_eq!(product.name(), &name);
        assert_eq!(product.description(), &description);
        assert_eq!(product.price(), &price);
        assert_eq!(product.available_quantity(), initial_quantity);
        assert_eq!(product.status(), &ProductStatus::Draft);
    }
    
    #[test]
    fn test_create_product_with_empty_name() {
        // Arrange
        let id = ProductId::new();
        let name = "".to_string();
        let description = "A test product".to_string();
        let price = Money::new(29.99, Currency::USD).unwrap();
        let initial_quantity = 100;
        
        // Act
        let result = Product::new(
            id,
            name,
            description,
            price,
            initial_quantity,
            CategoryId::new(),
        );
        
        // Assert
        assert!(result.is_err());
        match result {
            Err(DomainError::ValidationError(msg)) => {
                assert_eq!(msg, "Product name cannot be empty");
            },
            _ => panic!("Expected ValidationError"),
        }
    }
    
    #[test]
    fn test_update_price() {
        // Arrange
        let mut product = create_test_product();
        let new_price = Money::new(39.99, Currency::USD).unwrap();
        
        // Act
        let result = product.update_price(new_price.clone());
        
        // Assert
        assert!(result.is_ok());
        assert_eq!(product.price(), &new_price);
    }
    
    #[test]
    fn test_update_price_with_zero_value() {
        // Arrange
        let mut product = create_test_product();
        let new_price = Money::new(0.0, Currency::USD).unwrap();
        
        // Act
        let result = product.update_price(new_price);
        
        // Assert
        assert!(result.is_err());
        match result {
            Err(DomainError::ValidationError(msg)) => {
                assert_eq!(msg, "Product price must be positive");
            },
            _ => panic!("Expected ValidationError"),
        }
    }
    
    #[test]
    fn test_activate_product() {
        // Arrange
        let mut product = create_test_product();
        assert_eq!(product.status(), &ProductStatus::Draft);
        
        // Act
        let result = product.activate();
        
        // Assert
        assert!(result.is_ok());
        assert_eq!(product.status(), &ProductStatus::Active);
    }
    
    #[test]
    fn test_cannot_activate_discontinued_product() {
        // Arrange
        let mut product = create_test_product();
        product.discontinue().unwrap();
        assert_eq!(product.status(), &ProductStatus::Discontinued);
        
        // Act
        let result = product.activate();
        
        // Assert
        assert!(result.is_err());
        match result {
            Err(DomainError::InvalidStateTransition(msg)) => {
                assert_eq!(msg, "Cannot activate a discontinued product");
            },
            _ => panic!("Expected InvalidStateTransition"),
        }
    }
    
    // Helper function to create a test product
    fn create_test_product() -> Product {
        Product::new(
            ProductId::new(),
            "Test Product".to_string(),
            "A test product".to_string(),
            Money::new(29.99, Currency::USD).unwrap(),
            100,
            CategoryId::new(),
        ).unwrap()
    }
}
```

**集成测试示例**:

```rust
// tests/api/product_api_tests.rs
use crate::helpers::{spawn_app, TestApp};
use uuid::Uuid;

#[tokio::test]
async fn create_product_returns_201_for_valid_data() {
    // Arrange
    let app = spawn_app().await;
    let client = reqwest::Client::new();
    
    let auth_token = app.get_admin_token().await;
    
    let test_cases = vec![
        (
            "Basic product",
            json!({
                "name": "Test Product",
                "description": "A test product",
                "price": 29.99,
                "initial_quantity": 100,
                "category_id": Uuid::new_v4().to_string()
            }),
        ),
        (
            "Minimum price",
            json!({
                "name": "Cheap Product",
                "description": "A cheap product",
                "price": 0.01,
                "initial_quantity": 100,
                "category_id": Uuid::new_v4().to_string()
            }),
        ),
    ];
    
    for (test_name, body) in test_cases {
        // Act
        let response = client
            .post(&format!("{}/api/products", &app.address))
            .header("Content-Type", "application/json")
            .header("Authorization", format!("Bearer {}", auth_token))
            .json(&body)
            .send()
            .await
            .expect(&format!("Failed to execute request for {}", test_name));
            
        // Assert
        assert_eq!(
            201, 
            response.status().as_u16(),
            "Test case '{}' failed with status {}",
            test_name,
            response.status()
        );
        
        // Verify response structure
        let json_response = response.json::<serde_json::Value>().await
            .expect(&format!("Failed to parse response for {}", test_name));
            
        assert!(json_response.get("product_id").is_some(), 
            "Test case '{}' response missing product_id", test_name);
        assert!(json_response.get("message").is_some(), 
            "Test case '{}' response missing message", test_name);
    }
}

#[tokio::test]
async fn create_product_returns_400_for_invalid_data() {
    // Arrange
    let app = spawn_app().await;
    let client = reqwest::Client::new();
    
    let auth_token = app.get_admin_token().await;
    
    let test_cases = vec![
        (
            "Empty name",
            json!({
                "name": "",
                "description": "A test product",
                "price": 29.99,
                "initial_quantity": 100,
                "category_id": Uuid::new_v4().to_string()
            }),
        ),
        (
            "Zero price",
            json!({
                "name": "Zero Price Product",
                "description": "A test product",
                "price": 0.0,
                "initial_quantity": 100,
                "category_id": Uuid::new_v4().to_string()
            }),
        ),
        (
            "Negative price",
            json!({
                "name": "Negative Price Product",
                "description": "A test product",
                "price": -10.0,
                "initial_quantity": 100,
                "category_id": Uuid::new_v4().to_string()
            }),
        ),
    ];
    
    for (test_name, body) in test_cases {
        // Act
        let response = client
            .post(&format!("{}/api/products", &app.address))
            .header("Content-Type", "application/json")
            .header("Authorization", format!("Bearer {}", auth_token))
            .json(&body)
            .send()
            .await
            .expect(&format!("Failed to execute request for {}", test_name));
            
        // Assert
        assert_eq!(
            400, 
            response.status().as_u16(),
            "Test case '{}' failed with status {}",
            test_name,
            response.status()
        );
        
        // Verify response contains error information
        let json_response = response.json::<serde_json::Value>().await
            .expect(&format!("Failed to parse response for {}", test_name));
            
        assert!(json_response.get("error").is_some(), 
            "Test case '{}' response missing error field", test_name);
    }
}

#[tokio::test]
async fn get_product_returns_200_for_existing_product() {
    // Arrange
    let app = spawn_app().await;
    let product_id = app.create_test_product().await;
    let client = reqwest::Client::new();
    
    // Act
    let response = client
        .get(&format!("{}/api/products/{}", &app.address, product_id))
        .send()
        .await
        .expect("Failed to execute request");
        
    // Assert
    assert_eq!(200, response.status().as_u16());
    
    let product = response.json::<serde_json::Value>().await
        .expect("Failed to parse response");
        
    assert_eq!(product["id"], product_id);
    assert!(product.get("name").is_some());
    assert!(product.get("price").is_some());
    assert!(product.get("available_quantity").is_some());
}

#[tokio::test]
async fn get_product_returns_404_for_nonexistent_product() {
    // Arrange
    let app = spawn_app().await;
    let client = reqwest::Client::new();
    let nonexistent_id = Uuid::new_v4().to_string();
    
    // Act
    let response = client
        .get(&format!("{}/api/products/{}", &app.address, nonexistent_id))
        .send()
        .await
        .expect("Failed to execute request");
        
    // Assert
    assert_eq!(404, response.status().as_u16());
}
```

**性能测试示例**:

```rust
// benches/inventory_benchmark.rs
use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use std::sync::Arc;
use tokio::runtime::Runtime;

use your_crate::application::inventory_service::InventoryService;
use your_crate::domain::model::inventory::{InventoryItem, InventoryItemId};
use your_crate::domain::model::product::ProductId;
use your_crate::domain::model::warehouse::WarehouseId;
use your_crate::infrastructure::persistence::in_memory::InMemoryInventoryRepository;

fn inventory_reservation_benchmark(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("inventory_operations");
    
    for concurrent_requests in [1, 10, 50, 100].iter() {
        group.throughput(Throughput::Elements(*concurrent_requests as u64));
        group.bench_with_input(
            BenchmarkId::new("reserve_inventory", concurrent_requests),
            concurrent_requests,
            |b, &concurrent_requests| {
                b.to_async(&rt).iter(|| async {
                    let repository = Arc::new(InMemoryInventoryRepository::new());
                    let event_publisher = Arc::new(NullEventPublisher::new());
                    let service = InventoryService::new(repository.clone(), event_publisher);
                    
                    // 准备测试数据
                    let inventory_id = InventoryItemId::new();
                    let product_id = ProductId::new();
                    let warehouse_id = WarehouseId::new();
                    
                    let inventory_item = InventoryItem::new(
                        inventory_id.clone(),
                        product_id,
                        warehouse_id,
                        1000, // 足够大的初始库存
                    );
                    
                    repository.save(&inventory_item).await.unwrap();
                    
                    // 并发执行多个预留请求
                    let futures = (0..concurrent_requests)
                        .map(|_| {
                            let service = service.clone();
                            let inventory_id = inventory_id.clone();
                            
                            async move {
                                let command = ReserveInventoryCommand {
                                    inventory_id: inventory_id.to_string(),
                                    quantity: 1,
                                };
                                
                                service.reserve_inventory(command).await
                            }
                        })
                        .collect::<Vec<_>>();
                        
                    futures::future::join_all(futures).await
                })
            },
        );
    }
    
    group.finish();
}

criterion_group!(benches, inventory_reservation_benchmark);
criterion_main!(benches);
```

**属性测试示例**:

```rust
// tests/property/order_properties.rs
use proptest::prelude::*;
use your_crate::domain::model::order::{Order, OrderId, OrderStatus};
use your_crate::domain::model::customer::CustomerId;
use your_crate::domain::model::product::ProductId;
use your_crate::domain::model::money::{Money, Currency};
use your_crate::domain::model::address::Address;

// 策略：生成有效的订单项
fn order_item_strategy() -> impl Strategy<Value = (String, u32, f64)> {
    (
        "[A-Za-z0-9]{8}".prop_map(|s| s.to_string()),  // 产品名称
        1..100u32,                                      // 数量
        (1..10000).prop_map(|n| n as f64 / 100.0)      // 单价 (0.01-100.00)
    )
}

// 策略：生成订单
fn order_strategy() -> impl Strategy<Value = Order> {
    (
        prop::collection::vec(order_item_strategy(), 0..10)  // 0-10个订单项
    ).prop_map(|items| {
        let order_id = OrderId::new();
        let customer_id = CustomerId::new();
        let address = Address::new(
            "123 Main St".to_string(),
            "Anytown".to_string(),
            "CA".to_string(),
            "US".to_string(),
            "12345".to_string(),
        ).unwrap();
        
        let mut order = Order::new(order_id, customer_id, address

```rust
        let mut order = Order::new(order_id, customer_id, address);
        
        // 添加订单项
        for (product_name, quantity, price) in items {
            let _ = order.add_item(
                ProductId::new(),
                product_name,
                quantity,
                Money::new(price, Currency::USD).unwrap(),
            );
        }
        
        order
    })
}

proptest! {
    // 验证特性：添加商品后总金额增加
    #[test]
    fn adding_item_increases_total_amount(
        mut order in order_strategy(),
        product_name in "[A-Za-z0-9]{8}".prop_map(String::from),
        quantity in 1..100u32,
        price in (1..10000).prop_map(|n| n as f64 / 100.0)
    ) {
        // 初始总金额
        let initial_total = order.total_amount().value();
        
        // 添加商品
        let _ = order.add_item(
            ProductId::new(),
            product_name,
            quantity,
            Money::new(price, Currency::USD).unwrap(),
        );
        
        // 最终总金额
        let final_total = order.total_amount().value();
        
        // 验证总金额增加
        prop_assert!(final_total > initial_total);
        
        // 验证增加的金额等于新增商品的小计
        let expected_increase = price * (quantity as f64);
        prop_assert!((final_total - initial_total - expected_increase).abs() < 0.001);
    }
    
    // 验证特性：订单状态转换遵循业务规则
    #[test]
    fn order_state_transitions_follow_business_rules(mut order in order_strategy()) {
        // 只有非空的草稿订单可以提交
        if order.items().is_empty() {
            prop_assert!(order.submit().is_err());
        } else {
            // 草稿订单可以提交
            prop_assert_eq!(order.status(), &OrderStatus::Draft);
            prop_assert!(order.submit().is_ok());
            prop_assert_eq!(order.status(), &OrderStatus::Submitted);
            
            // 已提交的订单可以标记为已付款
            prop_assert!(order.mark_as_paid().is_ok());
            prop_assert_eq!(order.status(), &OrderStatus::Paid);
            
            // 已付款的订单不能再次标记为已付款
            prop_assert!(order.mark_as_paid().is_err());
            
            // 已付款的订单不能重新提交
            prop_assert!(order.submit().is_err());
        }
    }
    
    // 验证特性：草稿状态才能修改订单项
    #[test]
    fn only_draft_orders_can_be_modified(
        mut order in order_strategy(),
        product_name in "[A-Za-z0-9]{8}".prop_map(String::from),
        quantity in 1..100u32,
        price in (1..10000).prop_map(|n| n as f64 / 100.0)
    ) {
        // 如果有订单项，将订单提交
        if !order.items().is_empty() {
            let _ = order.submit();
            
            // 验证非草稿状态不能添加、删除商品
            let product_id = ProductId::new();
            prop_assert!(order.add_item(
                product_id.clone(),
                product_name,
                quantity,
                Money::new(price, Currency::USD).unwrap(),
            ).is_err());
            
            if let Some(item) = order.items().first() {
                prop_assert!(order.remove_item(&item.product_id()).is_err());
            }
        }
    }
}
```

### CI/CD 配置示例

```yaml
# .github/workflows/ci.yml
name: Rust CI Pipeline

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main, develop ]

env:
  CARGO_TERM_COLOR: always
  RUSTC_WRAPPER: sccache
  SCCACHE_GHA_ENABLED: "true"
  RUSTFLAGS: "-D warnings"

jobs:
  check:
    name: Check
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt, clippy
          
      - name: Cache dependencies
        uses: Swatinem/rust-cache@v2
        
      - name: Check formatting
        run: cargo fmt --all -- --check
        
      - name: Check with clippy
        run: cargo clippy --all-targets --all-features -- -D warnings

  test:
    name: Test
    runs-on: ubuntu-latest
    services:
      postgres:
        image: postgres:14
        env:
          POSTGRES_PASSWORD: postgres
          POSTGRES_USER: postgres
          POSTGRES_DB: test_db
        ports:
          - 5432:5432
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
          
      redis:
        image: redis:7
        ports:
          - 6379:6379
        options: >-
          --health-cmd "redis-cli ping"
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
          
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        
      - name: Cache dependencies
        uses: Swatinem/rust-cache@v2
        
      - name: Run unit tests
        run: cargo test --lib
        
      - name: Run integration tests
        run: cargo test --test "*"
        env:
          DATABASE_URL: postgres://postgres:postgres@localhost:5432/test_db
          REDIS_URL: redis://localhost:6379
          
      - name: Run doc tests
        run: cargo test --doc

  build:
    name: Build
    runs-on: ubuntu-latest
    needs: [check, test]
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        
      - name: Cache dependencies
        uses: Swatinem/rust-cache@v2
        
      - name: Build in release mode
        run: cargo build --release
        
      - name: Upload artifacts
        uses: actions/upload-artifact@v3
        with:
          name: service-binary
          path: target/release/your-service-name
          
  benchmark:
    name: Benchmark
    runs-on: ubuntu-latest
    needs: [build]
    if: github.event_name == 'pull_request'
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        
      - name: Cache dependencies
        uses: Swatinem/rust-cache@v2
        
      - name: Run benchmarks
        run: cargo bench -- --output-format bencher | tee bench_result.txt
        
      - name: Store benchmark result
        uses: benchmark-action/github-action-benchmark@v1
        with:
          name: Rust Benchmark
          tool: 'cargo'
          output-file-path: bench_result.txt
          github-token: ${{ secrets.GITHUB_TOKEN }}
          auto-push: true
          
  deploy:
    name: Deploy
    runs-on: ubuntu-latest
    needs: [check, test, build]
    if: github.ref == 'refs/heads/main'
    steps:
      - uses: actions/checkout@v3
      
      - name: Download artifacts
        uses: actions/download-artifact@v3
        with:
          name: service-binary
          path: ./
          
      - name: Make binary executable
        run: chmod +x ./your-service-name
        
      - name: Docker login
        uses: docker/login-action@v2
        with:
          username: ${{ secrets.DOCKER_HUB_USERNAME }}
          password: ${{ secrets.DOCKER_HUB_ACCESS_TOKEN }}
          
      - name: Build and push Docker image
        uses: docker/build-push-action@v4
        with:
          context: .
          push: true
          tags: yourusername/your-service-name:latest,yourusername/your-service-name:${{ github.sha }}
          
      - name: Deploy to production
        uses: appleboy/ssh-action@v0.1.10
        with:
          host: ${{ secrets.SSH_HOST }}
          username: ${{ secrets.SSH_USERNAME }}
          key: ${{ secrets.SSH_PRIVATE_KEY }}
          script: |
            cd /opt/services
            docker-compose pull
            docker-compose up -d
```

### Dockerfile示例

```dockerfile
# Dockerfile
FROM debian:bullseye-slim

# 添加非root用户
RUN groupadd -r appuser && useradd -r -g appuser appuser

# 创建应用目录
WORKDIR /app

# 复制编译好的二进制文件
COPY your-service-name /app/
COPY config/ /app/config/

# 设置权限
RUN chown -R appuser:appuser /app && \
    chmod +x /app/your-service-name

# 暴露应用端口
EXPOSE 8080

# 定义健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

# 使用非root用户运行应用
USER appuser

# 设置环境变量
ENV APP_ENV=production

# 运行应用
CMD ["/app/your-service-name"]
```

### 监控与可观测性配置

```rust
// src/infrastructure/observability/mod.rs
use opentelemetry::global;
use opentelemetry::sdk::trace::{self, Sampler};
use opentelemetry::sdk::Resource;
use opentelemetry::KeyValue;
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, Registry};
use tracing_opentelemetry::OpenTelemetryLayer;

pub fn init_telemetry(service_name: &str, otlp_endpoint: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 初始化OpenTelemetry追踪
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(otlp_endpoint)
        )
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::AlwaysOn)
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    KeyValue::new("deployment.environment", std::env::var("APP_ENV").unwrap_or_else(|_| "development".into())),
                ]))
        )
        .install_batch(opentelemetry::runtime::Tokio)?;
        
    // 创建OpenTelemetry层
    let telemetry_layer = OpenTelemetryLayer::new(tracer);
    
    // 初始化日志订阅者
    Registry::default()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(telemetry_layer)
        .init();
        
    Ok(())
}

pub fn shutdown_telemetry() {
    // 确保所有追踪上报完成
    global::shutdown_tracer_provider();
}

// 可用于埋点的工具宏
#[macro_export]
macro_rules! trace_fn {
    ($name:expr) => {
        let _span = tracing::info_span!($name).entered();
    };
    ($name:expr, $($key:expr => $value:expr),+ $(,)?) => {
        let _span = tracing::info_span!($name, $($key = $value),+).entered();
    };
}
```

### 自动化容量测试

```rust
// tests/capacity/load_test.rs
use goose::prelude::*;

// 定义负载测试任务
async fn product_list(user: &mut GooseUser) -> TransactionResult {
    let _response = user.get("api/products").await?;
    Ok(())
}

async fn product_detail(user: &mut GooseUser) -> TransactionResult {
    // 获取一个随机产品ID
    let product_ids = ["product1", "product2", "product3", "product4", "product5"];
    let product_id = product_ids[rand::random::<usize>() % product_ids.len()];
    
    let _response = user.get(&format!("api/products/{}", product_id)).await?;
    Ok(())
}

async fn create_order(user: &mut GooseUser) -> TransactionResult {
    let order_data = serde_json::json!({
        "customer_id": "customer123",
        "shipping_address": {
            "street": "123 Main St",
            "city": "Anytown",
            "state": "CA",
            "country": "US",
            "postal_code": "12345"
        }
    });
    
    let _response = user.post("api/orders", &serde_json::to_string(&order_data)?)
        .await?;
    Ok(())
}

// 定义测试场景
#[tokio::main]
async fn main() -> Result<(), GooseError> {
    GooseAttack::initialize()?
        .register_scenario(
            scenario!("BrowseProducts")
                .set_weight(70)?
                .register_transaction(transaction!(product_list))
                .register_transaction(transaction!(product_detail).set_weight(5)?)
        )
        .register_scenario(
            scenario!("CheckoutProcess")
                .set_weight(30)?
                .register_transaction(transaction!(create_order))
        )
        .execute()
        .await?;
        
    Ok(())
}
```

## 10. 总结与展望

通过本文的系统性探讨，我们从概念模型到Rust工程实现展开了全面分析：

1. **概念模型是领域理解的关键**：概念模型提供了业务逻辑和技术实现之间的桥梁，有效隔离了业务复杂性和技术复杂性。

2. **Rust的类型系统适合表达领域规则**：Rust提供了强大的类型系统、所有权模型和特征系统，能够在编译时验证业务规则并确保安全性。

3. **分层架构促进关注点分离**：通过领域层、应用层、基础设施层和接口层的有效分离，系统变得可维护和可扩展。

4. **事件驱动架构提高系统弹性**：松耦合、事件驱动的设计让系统更能适应变化，特别是在分布式环境中。

5. **工程实践推动理论到实践转化**：测试、CI/CD、监控等工程实践确保了概念模型能够被准确地转化为生产级的软件系统。

### 未来展望

1. **面向领域特定语言（DSL）的Rust工具**：开发更多辅助将概念模型转化为Rust代码的工具，简化从领域专家到开发者的转换过程。

2. **编译时验证的拓展**：进一步探索如何利用Rust的类型系统和宏系统验证更复杂的业务规则，减少运行时错误。

3. **领域驱动设计工具生态**：构建更完善的Rust DDD工具生态，包括代码生成、模式检测等支持设施。

4. **基于事件溯源的通用框架**：开发成熟的事件溯源和CQRS框架，简化这些架构模式在Rust中的应用。

5. **领域特定优化**：针对不同行业领域开发优化的领域模型库和工具链，加速特定领域的应用开发。

通过坚持概念模型与工程实现的有效映射，我们可以构建既能准确反映业务需求，又具备Rust语言高性能和安全性特点的软件系统。这种方法论的持续发展将为复杂系统的开发提供更可靠的路径。

---

## 思维导图

```text
从概念模型到工程实现: Rust语言视角下的分层架构与技术映射
├── 1. 引言: 复杂性挑战与应对
│   ├── 业务复杂性与技术复杂性的双重挑战
│   ├── 概念模型的桥接作用
│   ├── Rust语言的独特优势
│   └── 文档结构与阅读指南
├── 2. 概念模型与领域驱动设计
│   ├── 概念模型定义与作用
│   ├── DDD核心概念
│   │   ├── 实体与值对象
│   │   ├── 聚合与边界
│   │   ├── 领域服务
│   │   ├── 领域事件
│   │   └── 限界上下文
│   ├── Rust与DDD的亲和性
│   └── 概念模型到代码的映射路径
├── 3. Rust类型系统与概念映射
│   ├── 实体与值对象映射
│   ├── 聚合与边界表达
│   ├── 关系映射策略
│   ├── 领域规则与不变性实现
│   └── 类型映射优势与局限分析
├── 4. 行为验证与形式化方法
│   ├── 编译时验证与类型安全
│   ├── 属性测试验证业务规则
│   ├── 状态不变性验证
│   └── 模型检验技术
├── 5. 分层架构原则
│   ├── 清晰架构与六边形架构
│   ├── 层次职责与边界
│   ├── 依赖倒置原则应用
│   └── Rust项目结构示例
├── 6. Rust技术栈选型
│   ├── 领域层技术选择
│   ├── 应用层框架与库
│   ├── 基础设施层实现方案
│   └── 接口层技术选择
├── 7. 高级架构模式与Rust实现
│   ├── CQRS模式
│   ├── 事件溯源
│   ├── 微服务架构
│   └── 分布式事务处理
├── 8. 工程实践案例
│   ├── 电子商务系统示例
│   ├── 实时库存管理系统
│   └── 事件驱动微服务架构
├── 9. 工程化最佳实践
│   ├── 测试策略
│   ├── CI/CD配置
│   ├── 监控与可观测性
│   └── 容量规划与自动化测试
└── 10. 总结与展望
    ├── 关键概念回顾
    ├── 实践经验总结
    ├── 方法论提炼
    └── 未来发展方向
```

希望本文对您理解如何从概念模型到Rust工程实现的全过程有所帮助！
