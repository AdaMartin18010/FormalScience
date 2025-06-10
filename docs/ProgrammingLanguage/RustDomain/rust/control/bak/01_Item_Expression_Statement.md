# Item、Expression 和 Statement

在 Rust 中，"items"、"expressions" 和 "statements" 是三个基本的概念，
它们在程序的结构和执行中扮演不同的角色。

下面是它们的定义、区别、联系和解释：

## Items

- **定义**：Items 是 Rust 程序中的声明，它们定义了可以被引用的实体，如函数、结构体、枚举、模块、常量、静态变量和特性（traits）。
- **特点**：Items 通常不执行操作，它们只是定义了程序中可以调用或使用的结构和数据类型。

## Expressions

- **定义**：Expressions 是执行计算并产生值的代码片段。它们可以是变量、字面量、函数调用、运算符等。
- **特点**：Expressions 总是有返回值，即使是单元类型 `()`。

## Statements

- **定义**：Statements 是执行操作但不产生值的代码片段。它们用于执行副作用，如变量声明、循环、条件语句等。
- **特点**：Statements 没有返回值，它们主要用于控制程序流程。

## 区别

- **返回值**：Expressions 总是产生一个值，而 Statements 不产生值。
- **目的**：Expressions 用于计算和产生结果，Statements 用于执行操作和控制程序流程。
- **组成**：Statements 可以包含 expressions，但 expressions 不能包含 statements（除了表达式语句）。

## 联系

- **嵌套**：Statements 可以包含 expressions，例如，在 `if` 语句的条件中可以使用 expressions。
- **执行**：在 Rust 中，statements 通常执行顺序操作，而 expressions 可以在 statements 中被调用以产生值。
- **表达式语句**：Rust 允许将 expressions 用作 statements，称为表达式语句。
    例如，`let x = 42;` 是一个表达式语句，因为它包含一个 expression `42` 并赋值给变量 `x`。

## 解释

- **程序结构**：Items 为 Rust 程序提供了结构，定义了可以被引用的实体。
- **程序行为**：Expressions 描述了程序的行为，它们是程序中进行操作和计算的基本单元。
- **程序控制**：Statements 控制程序的执行流程，如条件判断、循环等。

## 示例

```rust
fn main() {
    // Item: 函数声明
    fn add(a: i32, b: i32) -> i32 {
        a + b // Expression: 计算和返回值
    }

    // Statement: 变量声明，没有返回值
    let x = 5;

    // Expression used as a statement: 表达式语句，赋值操作
    let y = add(x, 3); // 调用函数，产生一个值

    // Statement: 控制流语句，没有返回值
    if y > 10 {
        println!("y is greater than 10");
    }
}
```

在这个示例中，`add` 是一个 item，`a + b` 和 `add(x, 3)` 是 expressions，而 `let x = 5;` 和 `if y > 10 { ... }` 是 statements。
Expressions 用于计算值，而 statements 用于控制程序的执行流程和执行副作用。
