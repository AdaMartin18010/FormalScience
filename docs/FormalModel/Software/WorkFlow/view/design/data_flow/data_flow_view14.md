
# Rust类型系统的可变性、不变性、协变性、逆变性与概念模型的映射关系

## 1. 可变性(Mutability)与不变性(Immutability)的领域映射

### 值对象的不变性实现

在领域驱动设计中，值对象(Value Object)应当是不可变的。Rust的不变性特性与此完美匹配：

```rust
// 值对象 - 完全不可变实现
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Money {
    amount: i64,  // 以分为单位存储
    currency: Currency,
}

impl Money {
    pub fn new(amount: i64, currency: Currency) -> Result<Self, DomainError> {
        if amount < 0 {
            return Err(DomainError::ValidationError("金额不能为负".into()));
        }
        
        Ok(Self { amount, currency })
    }
    
    // 不可变操作 - 返回新实例
    pub fn add(&self, other: &Money) -> Result<Money, DomainError> {
        if self.currency != other.currency {
            return Err(DomainError::ValidationError("货币类型不匹配".into()));
        }
        
        Ok(Money {
            amount: self.amount + other.amount,
            currency: self.currency.clone(),
        })
    }
    
    // 只读访问器
    pub fn amount(&self) -> i64 {
        self.amount
    }
    
    pub fn currency(&self) -> &Currency {
        &self.currency
    }
}
```

**映射关系**:

- Rust的默认不可变性使值对象的实现更加自然
- 通过`&self`方法保证了值对象不会被修改
- 操作返回新实例而非修改现有实例，符合值对象语义

### 实体的可控可变性

实体(Entity)需要有控制的可变性，Rust通过`&mut self`提供了精确控制：

```rust
pub struct Order {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    status: OrderStatus,
    total: Money,
    version: u32,  // 用于乐观并发控制
}

impl Order {
    // 修改状态的方法必须接受&mut self
    pub fn add_item(&mut self, item: OrderItem) -> Result<(), DomainError> {
        // 业务规则验证
        if self.status != OrderStatus::Draft {
            return Err(DomainError::InvalidOperation("只有草稿订单可以添加商品".into()));
        }
        
        // 添加项目
        self.items.push(item.clone());
        
        // 重新计算总金额
        let item_total = item.calculate_subtotal();
        self.total = self.total.add(&item_total)?;
        
        // 增加版本号 - 实现乐观锁
        self.version += 1;
        
        Ok(())
    }
    
    // 只读访问使用&self
    pub fn total(&self) -> &Money {
        &self.total
    }
}
```

**映射关系**:

- 通过`&mut self`精确控制实体可修改的操作
- 将实体修改限制在一组明确定义的方法中，满足实体封装要求
- 修改操作内置业务规则验证，确保实体始终处于有效状态

## 2. 协变性(Covariance)与领域建模

协变性是指当A是B的子类型时，容器类型`Container<A>`也是`Container<B>`的子类型的特性。在Rust中，引用类型`&T`和`Box<T>`是协变的。

### 领域服务中的协变关系

```rust
// 接口定义
trait PaymentProcessor {
    fn process_payment(&self, amount: &Money) -> Result<PaymentId, PaymentError>;
}

// 具体实现
struct CreditCardProcessor { /* ... */ }
struct PayPalProcessor { /* ... */ }

impl PaymentProcessor for CreditCardProcessor {
    fn process_payment(&self, amount: &Money) -> Result<PaymentId, PaymentError> {
        // 信用卡支付实现
        // ...
    }
}

impl PaymentProcessor for PayPalProcessor {
    fn process_payment(&self, amount: &Money) -> Result<PaymentId, PaymentError> {
        // PayPal支付实现
        // ...
    }
}

// 支付服务 - 利用协变性接受任何PaymentProcessor实现
pub struct PaymentService<P: PaymentProcessor> {
    processor: P,
}

impl<P: PaymentProcessor> PaymentService<P> {
    pub fn new(processor: P) -> Self {
        Self { processor }
    }
    
    pub fn charge_order(&self, order: &Order) -> Result<PaymentId, DomainError> {
        self.processor.process_payment(order.total())
            .map_err(|e| DomainError::PaymentError(e))
    }
}

// 使用示例
let credit_processor = CreditCardProcessor::new();
let payment_service = PaymentService::new(credit_processor);
```

**映射关系**:

- 协变性使得领域服务能够接受不同的具体实现，实现依赖反转
- 可以将具体的处理实现替换为更具体的子类型，保持类型安全
- 支持策略模式等常见领域设计模式

### 实体集合中的协变关系

```rust
pub struct ShoppingCart {
    items: Vec<Box<dyn CartItem>>,  // 使用trait object
}

pub trait CartItem {
    fn name(&self) -> &str;
    fn unit_price(&self) -> &Money;
    fn quantity(&self) -> u32;
    fn subtotal(&self) -> Money;
}

// 实现CartItem的具体类型
pub struct ProductItem {
    product_id: ProductId,
    name: String,
    unit_price: Money,
    quantity: u32,
}

pub struct BundleItem {
    bundle_id: BundleId,
    name: String,
    products: Vec<ProductItem>,
    discount: Money,
}

impl CartItem for ProductItem {
    // 实现方法...
}

impl CartItem for BundleItem {
    // 实现方法...
}

impl ShoppingCart {
    pub fn add_item(&mut self, item: Box<dyn CartItem>) {
        self.items.push(item);
    }
    
    pub fn total(&self) -> Money {
        self.items.iter()
            .fold(Money::zero(Currency::USD), |acc, item| {
                acc.add(&item.subtotal()).unwrap_or(acc)
            })
    }
}
```

**映射关系**:

- 协变性允许`Box<ProductItem>`和`Box<BundleItem>`都能用作`Box<dyn CartItem>`
- 这种模式使领域模型能够表达"是一种"关系，同时保持类型安全
- 支持聚合根包含不同类型的实体或值对象

## 3. 逆变性(Contravariance)与回调函数

逆变性是指当A是B的子类型时，`Fn(B)`是`Fn(A)`的子类型。在Rust中，函数参数位置是逆变的。

### 领域事件处理中的逆变关系

```rust
// 领域事件基类
pub trait DomainEvent {
    fn event_type(&self) -> &str;
    fn occurred_at(&self) -> DateTime<Utc>;
}

// 具体事件类型
pub struct OrderPlacedEvent {
    order_id: OrderId,
    customer_id: CustomerId,
    amount: Money,
    timestamp: DateTime<Utc>,
}

impl DomainEvent for OrderPlacedEvent {
    fn event_type(&self) -> &str { "order_placed" }
    fn occurred_at(&self) -> DateTime<Utc> { self.timestamp }
}

// 事件处理器
type EventHandler<E> = Box<dyn Fn(&E) -> Result<(), Error>>;

// 事件总线
pub struct EventBus {
    // 利用逆变性：&OrderPlacedEvent可以传给需要&dyn DomainEvent的处理器
    handlers: HashMap<&'static str, Vec<EventHandler<dyn DomainEvent>>>,
}

impl EventBus {
    pub fn new() -> Self {
        Self { handlers: HashMap::new() }
    }
    
    pub fn register<E: DomainEvent + 'static>(
        &mut self,
        event_type: &'static str,
        handler: impl Fn(&E) -> Result<(), Error> + 'static,
    ) {
        // 将特定事件处理器包装为通用处理器
        let generic_handler: EventHandler<dyn DomainEvent> = Box::new(move |event| {
            // 尝试向下转型
            if let Some(specific_event) = event.downcast_ref::<E>() {
                handler(specific_event)
            } else {
                Ok(()) // 忽略不匹配的事件类型
            }
        });
        
        self.handlers.entry(event_type)
            .or_insert_with(Vec::new)
            .push(generic_handler);
    }
    
    pub fn publish<E: DomainEvent>(&self, event: &E) -> Result<(), Error> {
        if let Some(handlers) = self.handlers.get(event.event_type()) {
            for handler in handlers {
                handler(event)?;
            }
        }
        Ok(())
    }
}
```

**映射关系**:

- 逆变性允许将特定事件类型的处理器转换为更通用事件类型的处理器
- 支持事件驱动架构中的松耦合设计
- 符合开闭原则，可以添加新的事件类型而不修改现有代码

## 4. 类型不变性(Invariance)与聚合一致性

类型不变性是指类型既不是协变的也不是逆变的。在Rust中，`&mut T`是不变的，这对维护聚合一致性很有用。

### 聚合根一致性保证

```rust
pub struct Customer {
    id: CustomerId,
    name: String,
    email: Email,
    addresses: Vec<Address>,
    // ...其他领域属性
}

impl Customer {
    // 安全修改方法 - 通过&mut self确保所有更改都经过验证
    
    pub fn change_email(&mut self, email: Email) -> Result<(), DomainError> {
        // 业务规则验证
        if self.email == email {
            return Ok(()); // 无需更改
        }
        
        // 可能需要触发额外验证逻辑
        self.email = email;
        
        Ok(())
    }
    
    pub fn add_address(&mut self, address: Address) -> Result<(), DomainError> {
        if self.addresses.len() >= 5 {
            return Err(DomainError::ValidationError("地址数量超出限制".into()));
        }
        
        // 验证地址是否已存在
        if self.addresses.contains(&address) {
            return Err(DomainError::ValidationError("地址已存在".into()));
        }
        
        self.addresses.push(address);
        
        Ok(())
    }
    
    // 不提供内部集合的可变引用，防止绕过验证
    pub fn addresses(&self) -> &[Address] {
        &self.addresses
    }
    
    // 不提供这样的方法！这会破坏聚合一致性
    // pub fn addresses_mut(&mut self) -> &mut Vec<Address> {
    //     &mut self.addresses
    // }
}
```

**映射关系**:

- `&mut T`的不变性防止绕过聚合根的业务规则直接修改内部集合
- 通过控制可变访问，确保聚合边界内的所有修改都遵循业务规则
- 显式拒绝返回内部集合的可变引用，强制通过聚合根的方法进行修改

## 5. 借用检查器与并发领域模型

Rust的借用检查器对保证领域模型的线程安全和一致性至关重要：

```rust
// 线程安全的资源池示例
pub struct ResourcePool<R> {
    available: Arc<Mutex<Vec<R>>>,
    max_size: usize,
}

impl<R> ResourcePool<R> {
    pub fn new(initial_resources: Vec<R>, max_size: usize) -> Self {
        Self {
            available: Arc::new(Mutex::new(initial_resources)),
            max_size,
        }
    }
    
    pub fn acquire(&self) -> Result<ResourceGuard<R>, PoolError> {
        let mut resources = self.available.lock()
            .map_err(|_| PoolError::LockError)?;
            
        if let Some(resource) = resources.pop() {
            Ok(ResourceGuard {
                resource: Some(resource),
                pool: self.available.clone(),
            })
        } else {
            Err(PoolError::NoResourceAvailable)
        }
    }
    
    pub fn size(&self) -> Result<usize, PoolError> {
        let resources = self.available.lock()
            .map_err(|_| PoolError::LockError)?;
            
        Ok(resources.len())
    }
}

// 自动归还资源的守卫对象
pub struct ResourceGuard<R> {
    resource: Option<R>,
    pool: Arc<Mutex<Vec<R>>>,
}

impl<R> Drop for ResourceGuard<R> {
    fn drop(&mut self) {
        if let Some(resource) = self.resource.take() {
            if let Ok(mut resources) = self.pool.lock() {
                resources.push(resource);
            }
        }
    }
}

impl<R> Deref for ResourceGuard<R> {
    type Target = R;
    
    fn deref(&self) -> &Self::Target {
        self.resource.as_ref().unwrap()
    }
}
```

**映射关系**:

- 借用检查器在编译时防止数据竞争，确保共享资源的安全访问
- 类型系统与所有权规则共同实现基于资源获取即初始化(RAII)的设计模式
- 这些保证使得在并发环境中实现领域模型变得更加安全可靠

## 6. 泛型与抽象领域概念

Rust的泛型系统是实现抽象领域概念的强大工具：

```rust
// 通用仓储接口
#[async_trait]
pub trait Repository<T, ID> {
    async fn save(&self, entity: &T) -> Result<(), RepositoryError>;
    async fn find_by_id(&self, id: &ID) -> Result<Option<T>, RepositoryError>;
    async fn delete(&self, entity: &T) -> Result<(), RepositoryError>;
}

// 聚合根特征，限定可以被存储的实体
pub trait AggregateRoot {
    type Id: Clone + Send + Sync;
    
    fn id(&self) -> &Self::Id;
    fn version(&self) -> u64;
    fn increment_version(&mut self);
}

// 基于泛型的仓储实现，约束为聚合根
#[async_trait]
impl<T, ID, R> Repository<T, ID> for R 
where
    T: AggregateRoot<Id = ID> + Clone + Send + Sync + 'static,
    ID: Clone + Send + Sync + Eq + Hash + 'static,
    R: AggregateRepository<T, ID>,
{
    async fn save(&self, entity: &T) -> Result<(), RepositoryError> {
        self.save_aggregate(entity).await
    }
    
    async fn find_by_id(&self, id: &ID) -> Result<Option<T>, RepositoryError> {
        self.find_aggregate_by_id(id).await
    }
    
    async fn delete(&self, entity: &T) -> Result<(), RepositoryError> {
        self.delete_aggregate(entity).await
    }
}

// 实现聚合根的具体实体
impl AggregateRoot for Order {
    type Id = OrderId;
    
    fn id(&self) -> &Self::Id {
        &self.id
    }
    
    fn version(&self) -> u64 {
        self.version
    }
    
    fn increment_version(&mut self) {
        self.version += 1;
    }
}
```

**映射关系**:

- 泛型与特征约束实现了领域概念的抽象表达
- 通过类型参数约束，确保仓储只能存储符合聚合根特性的实体
- 支持依赖反转原则，领域层定义接口，基础设施层提供实现

## 总结

Rust类型系统的这些特性与概念模型的映射关系如下：

| Rust类型特性 | 概念模型映射 | 优势 |
|-------------|------------|------|
| 不变性(Immutability) | 值对象不可变性 | 确保值对象的一致性和线程安全 |
| 可变性(Mutability) | 实体受控修改 | 通过&mut self强制业务规则验证 |
| 协变性(Covariance) | 多态领域服务 | 支持策略模式和依赖注入 |
| 逆变性(Contravariance) | 事件处理系统 | 实现灵活的事件发布订阅模型 |
| 类型不变性(Invariance) | 聚合一致性 | 防止内部状态被绕过验证修改 |
| 借用检查器 | 并发领域模型 | 编译时保证线程安全 |
| 泛型约束 | 抽象领域概念 | 表达通用模式并强制领域规则 |

Rust的类型系统为概念模型的实现提供了强大的工具，不仅能够精确表达领域概念，还能在编译时捕获大量错误，
确保领域规则的正确实现。通过合理利用这些特性，可以构建既符合业务语义又保持高性能和安全性的领域模型。
