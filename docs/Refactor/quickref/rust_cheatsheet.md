# Rust 速查卡

> 单页速查 | 所有权 | 生命周期 | Traits | 错误处理

---

## 所有权规则

| 规则 | 说明 | 示例 |
|------|------|------|
| **规则1** | 每个值有且只有一个所有者 | `let s = String::from("hi");` |
| **规则2** | 所有者离开作用域，值被丢弃 | `}` 时调用 `drop` |
| **规则3** | 同一时间只能有一个可变引用 **或** 多个不可变引用 | `&mut T` vs `&T` |

### 所有权转移 vs 借用

| 操作 | 语法 | 所有权变化 | 使用场景 |
|------|------|------------|----------|
| 移动 | `let s2 = s1;` | s1失效，s2拥有 | 转移所有权 |
| 不可变借用 | `&s` | 不转移，只读 | 多次读取 |
| 可变借用 | `&mut s` | 不转移，可写 | 独占修改 |
| 克隆 | `s.clone()` | 复制新值 | 需要深拷贝 |
| Copy类型 | 自动复制 | 原值仍有效 | 栈上小类型 |

### Copy Trait 类型

| 类型 | 说明 |
|------|------|
| 所有整数类型 | `i32`, `u64`, `isize` 等 |
| 所有浮点类型 | `f32`, `f64` |
| 布尔类型 | `bool` |
| 字符类型 | `char` |
| 元组（仅含Copy类型） | `(i32, bool)` |
| 不可变引用 | `&T` |

---

## 生命周期标注

| 标注 | 含义 | 示例 |
|------|------|------|
| `'a` | 生命周期参数 | `fn foo<'a>(x: &'a str)` |
| `'static` | 程序整个生命周期 | `&'static str` |
| `&'a T` | 引用至少存活'a | `let r: &'a i32 = &x;` |
| `&'a mut T` | 可变引用存活'a | `fn longest<'a>(x: &'a str, y: &'a str) -> &'a str` |

### 常见生命周期模式

| 模式 | 代码 | 说明 |
|------|------|------|
| 输入=输出 | `fn f<'a>(x: &'a T) -> &'a U` | 返回与输入相同生命周期 |
| 多个输入 | `fn f<'a, 'b>(x: &'a T, y: &'b U)` | 不同生命周期 |
| 结构体 | `struct S<'a> { r: &'a str }` | 结构体含引用需标注 |
| 静态字符串 | `let s: &'static str = "hello";` | 编译期常量 |
| 生命周期省略 | 自动推断 | 满足三规则时省略 |

### 生命周期省略规则

1. 每个引用参数有独立生命周期
2. 单输入 → 返回值有相同生命周期
3. `&self`/`&mut self` → 返回值有相同生命周期

---

## 常用Trait

| Trait | 必需方法 | 用途 | 示例 |
|-------|----------|------|------|
| **Debug** | 自动派生 | 调试输出 | `#[derive(Debug)]` |
| **Clone** | `clone()` | 深拷贝 | `let c = a.clone();` |
| **Copy** | 标记trait | 按位复制 | `#[derive(Copy, Clone)]` |
| **Default** | `default()` | 默认值 | `T::default()` |
| **PartialEq** | `eq()` | 相等比较 | `a == b` |
| **Eq** | (标记) | 自反相等 | 整数等 |
| **PartialOrd** | `partial_cmp()` | 部分有序 | 浮点数 |
| **Ord** | `cmp()` | 全序 | 整数等 |
| **Hash** | `hash()` | 哈希计算 | `HashMap`键 |

### 智能指针Trait

| Trait | 方法 | 用途 |
|-------|------|------|
| **Deref** | `deref()` | 解引用重载 | `*rc` |
| **DerefMut** | `deref_mut()` | 可变解引用 | `*rc = val` |
| **Drop** | `drop()` | 析构函数 | RAII |
| **AsRef** | `as_ref()` | 引用转换 | 泛型API |
| **AsMut** | `as_mut()` | 可变引用转换 | 泛型API |
| **Borrow** | `borrow()` | 哈希键借用 | `HashMap` |

### 迭代器Trait

| Trait | 方法 | 用途 |
|-------|------|------|
| **Iterator** | `next()` | 基础迭代 | `for x in iter` |
| **IntoIterator** | `into_iter()` | 转换为迭代器 | `for x in vec` |
| **FromIterator** | `from_iter()` | 从迭代器构造 | `collect()` |
| **ExactSizeIterator** | `len()` | 精确长度 | `Iterator::len` |
| **DoubleEndedIterator** | `next_back()` | 双向迭代 | `rev()` |

### 函数式Trait

| Trait | 签名 | 用途 |
|-------|------|------|
| **Fn** | `fn call(&self, Args) -> Output` | 不可变闭包 |
| **FnMut** | `fn call_mut(&mut self, Args)` | 可变闭包 |
| **FnOnce** | `fn call_once(self, Args)` | 消耗性闭包 |

---

## 错误处理模式

### Result<T, E>

| 操作 | 方法 | 说明 |
|------|------|------|
| 解包 | `?` | 传播错误 | `let x = may_fail()?;` |
| 默认值 | `unwrap_or(default)` | 失败时用默认值 | `opt.unwrap_or(0)` |
| 计算默认 | `unwrap_or_else(f)` | 懒计算默认 | `opt.unwrap_or_else(|| 0)` |
| 映射 | `map(f)` | Ok时映射 | `r.map(|x| x+1)` |
| 映射Err | `map_err(f)` | Err时映射 | `r.map_err(|e| e.to_string())` |
| 链式 | `and_then(f)` | 扁平映射 | `r.and_then(parse)` |
| 转换Option | `ok()` / `err()` | Result→Option | `r.ok()` |

### Option<T>

| 操作 | 方法 | 说明 |
|------|------|------|
| 解包 | `?` | 传播None | `let x = opt?;` |
| 存在时 | `if let Some(x) = opt` | 模式匹配 |
| 默认值 | `unwrap_or(default)` | None时用默认值 |
| 过滤 | `filter(pred)` | 条件过滤 | `opt.filter(|x| x>0)` |
| 条件 | `unwrap_or_default()` | 类型默认值 |

### panic! vs Result

| 场景 | 选择 |
|------|------|
| 不可恢复错误 | `panic!` |
| 可恢复错误 | `Result` |
| 可选值可能缺失 | `Option` |
| 原型/测试 | `unwrap()` |
| 确定不会失败 | `expect("reason")` |

---

## 常用宏

| 宏 | 用途 | 示例 |
|----|------|------|
| `println!` | 格式化输出 | `println!("{}", x)` |
| `format!` | 创建字符串 | `let s = format!("{}", x)` |
| `vec!` | 创建向量 | `vec![1, 2, 3]` |
| `vec![val; n]` | 重复值 | `vec![0; 10]` |
| `assert!` | 断言 | `assert!(x > 0)` |
| `assert_eq!` | 相等断言 | `assert_eq!(a, b)` |
| `todo!` | 待实现标记 | `todo!("implement this")` |
| `unreachable!` | 不可达代码 | `unreachable!()` |

---

*打印版：A4横向，适合快速查阅*
