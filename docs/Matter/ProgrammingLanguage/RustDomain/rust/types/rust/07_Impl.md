# impl

在 Rust 中，`impl`（实现）是一个关键字，用于为类型提供具体的行为和实现特定的 trait。

以下是 `impl` 的定义和使用方式：

## 定义

`impl` 块用于以下目的：

- 为自定义类型（如结构体 `struct`、枚举 `enum` 或联合体 `union`）实现方法。
- 为类型实现特定的 trait。
- 提供类型定义的关联函数（关联到类型的函数，但不是属于特定实例的方法）。

### 使用方式

1. **为类型实现方法**:
   你可以为自定义类型定义方法，这些方法可以访问和修改类型的字段。

   ```rust
   struct Point {
       x: i32,
       y: i32,
   }

   impl Point {
       // 这是 Point 类型的关联函数，用于创建新实例
       fn new(x: i32, y: i32) -> Point {
           Point { x, y }
       }

       // 这是 Point 类型的实例方法，用于获取 x 和 y 的和
       fn sum(&self) -> i32 {
           self.x + self.y
       }
   }
   ```

2. **实现 trait**:
   当一个类型需要提供某个 trait 定义的行为时，可以使用 `impl` 来实现它。

   ```rust
   trait Animal {
       fn make_sound(&self);
   }

   struct Dog;

   impl Animal for Dog {
       fn make_sound(&self) {
           println!("Woof!");
       }
   }
   ```

3. **默认实现**:
   在 trait 中可以为方法提供默认实现，这些实现可以在 `impl` 块中被覆盖或重用。

   ```rust
   trait Animal {
       fn make_sound(&self);
       fn eat(&self) {
           println!("Eating...");
       }
   }

   impl Animal for Dog {
       fn make_sound(&self) {
           println!("Woof!");
       }

       // 重用默认的 eat 方法实现
   }
   ```

4. **使用 `impl` 块进行模式匹配**:
   在 `impl` 后面可以跟一个模式，用于匹配多种类型的实现。

   ```rust
   impl fmt::Display for Point {
       fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
           write!(f, "({}, {})", self.x, self.y)
       }
   }
   ```

5. **实现自动 trait**:
   有些 trait 如 `Send` 和 `Sync` 是自动的，但有时候需要显式实现。

   ```rust
   unsafe impl Send for Point {}
   ```

6. **实现关联类型**:
   在实现 trait 时，可以具体化 trait 中定义的关联类型。

   ```rust
   trait HasLength {
       type Len;
       fn length(&self) -> Self::Len;
   }

   impl HasLength for String {
       type Len = usize;
       fn length(&self) -> Self::Len {
           self.len()
       }
   }
   ```

`impl` 是 Rust 中实现类型行为的核心机制，它允许开发者为类型添加功能，满足 trait 定义的合约，以及提供类型特定的方法。
通过 `impl`，Rust 代码可以保持模块化和组织性，同时利用 trait 来实现代码的复用和多态性。
