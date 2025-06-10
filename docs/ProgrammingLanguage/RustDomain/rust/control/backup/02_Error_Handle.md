# Rust 错误处理

Rust 的错误处理编程是其核心编程范式的一部分，旨在确保程序的健壮性和安全性。
以下是 Rust 错误处理的关键概念和方法：

1. **`Result` 类型**:
   - 定义：`Result` 是 Rust 中用于错误处理的一个枚举类型，表示操作可能成功（`Ok`）或失败（`Err`）。
   - 使用：当函数可能失败时，通常返回 `Result<T, E>` 类型，其中 `T` 是操作成功时返回的值的类型，`E` 是失败时返回的错误类型的类型。

   ```rust
   fn divide(numerator: i32, denominator: i32) -> Result<i32, &'static str> {
       if denominator == 0 {
           Err("Cannot divide by zero")
       } else {
           Ok(numerator / denominator)
       }
   }
   ```

2. **`Option` 类型**:
   - 定义：`Option` 是 Rust 中的另一个枚举类型，表示值可能存在（`Some`）或不存在（`None`）。
   - 使用：通常用于表示可能缺失的值，与 `Result` 相比，`Option` 通常用于非错误情况的可选值。

3. **错误传播**:
   - 在 Rust 中，错误通过 `?` 运算符从函数中传播。如果 `Result` 是 `Err`，函数会立即返回这个错误，并将控制权转移给调用者。

   ```rust
   fn safe_divide(numerator: i32, denominator: i32) -> Result<i32, &'static str> {
       divide(numerator, denominator)?
   }
   ```

4. **匹配错误**:
   - 使用 `match` 语句来匹配 `Result` 或 `Option` 的不同变体，并根据错误类型执行不同的逻辑。

   ```rust
   match divide(10, 0) {
       Ok(result) => println!("Result is {}", result),
       Err(error) => println!("Error: {}", error),
   }
   ```

5. **自定义错误类型**:
   - 可以定义自定义错误类型来表示特定的错误情况。自定义错误类型通常实现 `std::fmt::Display` 和 `std::error::Error` trait。

   ```rust
   #[derive(Debug)]
   struct DivideByZero;

   impl std::fmt::Display for DivideByZero {
       fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
           write!(f, "Division by zero is not allowed.")
       }
   }

   impl std::error::Error for DivideByZero {}
   ```

6. **错误链（Error Chaining）**:
   - 使用 `?` 运算符时，Rust 会自动将内层 `Err` 的值封装到外层 `Err` 中，形成错误链，这有助于调试和错误追踪。

7. **错误处理策略**:
   - 在实际应用中，可能需要根据不同的错误类型采取不同的错误处理策略，如重试、记录日志、转换错误等。

8. **`expect` 和 `unwrap` 方法**:
   - `expect` 和 `unwrap` 是 `Result` 和 `Option` 类型的方法，用于在确定 `Result` 为 `Ok` 或 `Option` 为 `Some` 时获取内部值。如果为 `Err` 或 `None`，它们会 panic。

   ```rust
   let result = divide(10, 2).unwrap(); // 如果是 Err, 将 panic
   ```

9. **非致命错误处理**:
   - 在某些情况下，函数可能需要处理错误而不是传播，例如通过返回默认值或记录错误信息。

Rust 的错误处理模型鼓励开发者明确地处理潜在的错误情况，而不是使用例外机制，
这有助于编写更安全、更可预测的代码。
通过使用 `Result` 和 `Option` 类型，Rust 强制开发者面对可能的错误，从而减少运行时错误的可能性。
