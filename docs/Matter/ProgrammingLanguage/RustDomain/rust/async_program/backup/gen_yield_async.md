# rust生成器

在 Rust 2024 版本中，`gen`、`yield` 和 `next` 关键字为生成器和异步编程引入了新的特性。
以下是对这些关键字的定义、解释和使用说明，以及它们与其他语言特性的组合方式和编程建议。

## 📋 目录

  - [1.1 gen 关键字](#11-gen-关键字)
    - [1.1.1 yield 关键字](#111-yield-关键字)
    - [1.1.2 next 方法](#112-next-方法)
  - [1.2 与泛型结合](#12-与泛型结合)
    - [2.2.1 与生命周期结合](#221-与生命周期结合)
    - [2.2.2 与 trait bounds 结合](#222-与-trait-bounds-结合)
  - [1.3 异步流处理](#13-异步流处理)
  - [1.4 并发控制](#14-并发控制)
  - [1.5 映射和过滤](#15-映射和过滤)
    - [5.5.1 组合器模式](#551-组合器模式)
  - [1.6 Option 处理](#16-option-处理)
  - [1.7 RAII 模式](#17-raii-模式)
  - [1.8 异步资源管理](#18-异步资源管理)

---

## 1 1 基础定义与语法

### 1.1 gen 关键字

- **定义**: `gen` 用于定义一个生成器，它可以在执行过程中多次暂停和恢复。
- **用法**: 生成器可以是同步的，也可以是异步的。

```rust
// 同步生成器
let sync_gen = gen {
    yield 1;
    yield 2;
    yield 3;
};

// 异步生成器
let async_gen = gen async {
    yield 1;
    yield 2;
    yield 3;
};
```

#### 1.1.1 yield 关键字

- **定义**: `yield` 用于从生成器中返回一个值，并暂停生成器的执行。
- **用法**: 在生成器体内使用，返回一个值给调用者。

```rust
let numbers = gen {
    for i in 0..3 {
        yield i;
    }
};
```

#### 1.1.2 next 方法

- **定义**: `next` 是一个方法，用于从生成器中获取下一个值。
- **用法**: 对于同步生成器，直接调用；对于异步生成器，使用 `.await`。

```rust
// 同步迭代
while let Some(value) = sync_gen.next() {
    println!("{}", value);
}

// 异步迭代
while let Some(value) = async_gen.next().await {
    println!("{}", value);
}
```

## 2 2 高级特性组合

### 2.1 与泛型结合

```rust
fn generic_generator<T>(items: Vec<T>) -> impl Iterator<Item = T> {
    gen {
        for item in items {
            yield item;
        }
    }
}
```

#### 1.1.1 与生命周期结合

```rust
fn borrowed_generator<'a>(data: &'a [i32]) -> impl Iterator<Item = &'a i32> {
    gen {
        for item in data {
            yield item;
        }
    }
}
```

#### 1.1.2 与 trait bounds 结合

```rust
fn bounded_generator<T: Clone>(item: T) -> impl Iterator<Item = T> {
    gen {
        yield item.clone();
        yield item;
    }
}
```

## 3 3 异步编程模式

### 3.1 异步流处理

```rust
async fn process_stream<T: AsyncRead>(reader: T) -> impl Stream<Item = Result<Vec<u8>, io::Error>> {
    gen async {
        let mut buffer = [0u8; 1024];
        loop {
            match reader.read(&mut buffer).await {
                Ok(0) => break,
                Ok(n) => yield Ok(buffer[..n].to_vec()),
                Err(e) => yield Err(e),
            }
        }
    }
}
```

### 3.2 并发控制

```rust
async fn controlled_stream<T>(
    mut input: impl Stream<Item = T>,
    window_size: usize
) -> impl Stream<Item = Vec<T>> {
    gen async {
        let mut buffer = Vec::new();
        while let Some(item) = input.next().await {
            buffer.push(item);
            if buffer.len() >= window_size {
                yield std::mem::take(&mut buffer);
            }
        }
        if !buffer.is_empty() {
            yield buffer;
        }
    }
}
```

## 4 4 函数式编程模式

### 4.1 映射和过滤

```rust
fn transform_stream<T, U>(
    input: impl Iterator<Item = T>,
    f: impl Fn(T) -> Option<U>
) -> impl Iterator<Item = U> {
    gen {
        for item in input {
            if let Some(transformed) = f(item) {
                yield transformed;
            }
        }
    }
}
```

#### 1.1.1 组合器模式

```rust
fn combine_streams<T>(
    s1: impl Iterator<Item = T>,
    s2: impl Iterator<Item = T>
) -> impl Iterator<Item = T> {
    gen {
        for item in s1 {
            yield item;
        }
        for item in s2 {
            yield item;
        }
    }
}
```

## 5 5 错误处理模式

 *Result 处理

```rust
fn fallible_generator() -> impl Iterator<Item = Result<i32, Error>> {
    gen {
        for i in 0..5 {
            match expensive_operation(i) {
                Ok(value) => yield Ok(value),
                Err(e) => yield Err(e),
            }
        }
    }
}
```

### 5.1 Option 处理

```rust
fn optional_generator() -> impl Iterator<Item = Option<i32>> {
    gen {
        for i in 0..3 {
            if i % 2 == 0 {
                yield Some(i);
            } else {
                yield None;
            }
        }
    }
}
```

## 6 6 资源管理模式

### 6.1 RAII 模式

```rust
struct ManagedResource<T> {
    resource: T,
}

impl<T> ManagedResource<T> {
    fn generate_items(&self) -> impl Iterator<Item = i32> + '_ {
        gen {
            yield 1;
            // 资源会在迭代器销毁时自动清理
        }
    }
}
```

### 6.2 异步资源管理

```rust
async fn managed_async_stream() -> impl Stream<Item = Result<Data, Error>> {
    gen async {
        let mut connection = Connection::new().await?;
        while let Some(data) = connection.read_data().await? {
            yield Ok(data);
        }
        connection.close().await?;
    }
}
```

## 7 7 最佳实践建议

1. **保持生成器函数简单且单一职责**：避免在生成器中持有过多状态。
2. **适当使用类型注解提高代码可读性**：有助于理解生成器的输入和输出类型。
3. **考虑内存使用和性能影响**：特别是在处理大数据集时。
4. **合理处理错误情况**：使用 `Result` 和 `Option` 进行错误处理。
5. **注意资源的及时释放**：特别是在异步上下文中。
6. **使用文档注释说明生成器的行为**：提高代码的可维护性。
7. **考虑并发安全性**：在多线程环境中使用生成器时要小心。
8. **适当使用测试验证生成器行为**：确保生成器按预期工作。

通过这些特性和建议，Rust 2024 的生成器功能可以帮助开发者编写更高效、可读性更高的代码，特别是在需要处理复杂数据流和异步操作的场景中。
