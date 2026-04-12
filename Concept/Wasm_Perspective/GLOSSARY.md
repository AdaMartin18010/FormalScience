- --
topic: "WebAssembly 术语表 (GLOSSARY)"
dependencies: []
status: "review"
author: "FormalScience Project"
date: "2026-04-12"
version: "1.0.0"
tags: ["类型", "形式化", "定理", "算法", "计算"]
category: "reference"
priority: "medium"
- --

# WebAssembly 术语表 (GLOSSARY)

## 1. 📋 目录 {#-目录}

- [WebAssembly 术语表 (GLOSSARY)](#webassembly-术语表-glossary)
  - [1. 📋 目录 {#-目录}](#1--目录--目录)
  - [1. A {#a}](#1-a-a)
  - [2. B {#b}](#2-b-b)
  - [3. C {#c}](#3-c-c)
  - [4. D {#d}](#4-d-d)
  - [5. E {#e}](#5-e-e)
  - [6. F {#f}](#6-f-f)
  - [7. G {#g}](#7-g-g)
  - [8. H {#h}](#8-h-h)
  - [9. I {#i}](#9-i-i)
  - [10. J {#j}](#10-j-j)
  - [11. L {#l}](#11-l-l)
  - [12. M {#m}](#12-m-m)
  - [13. O {#o}](#13-o-o)
  - [14. P {#p}](#14-p-p)
  - [15. R {#r}](#15-r-r)
  - [16. S {#s}](#16-s-s)
  - [17. T {#t}](#17-t-t)
  - [18. V {#v}](#18-v-v)
  - [19. W {#w}](#19-w-w)
  - [20. Z {#z}](#20-z-z)
  - [21. 符号表 {#符号表}](#21-符号表-符号表)
  - [22. 缩略语 {#缩略语}](#22-缩略语-缩略语)
  - [关联网络](#关联网络)
    - [前向引用](#前向引用)
    - [后向引用](#后向引用)
    - [交叉链接](#交叉链接)

- --

## 1. A {#a}

- _Abstract Machine（抽象机器）_*
形式化的计算模型，定义状态空间与转移关系。Wasm 抽象机器 = 栈 + 内存 + 表 + 全局变量。

- _Abstract Interpretation（抽象解释）_*
静态分析技术，通过抽象域（如区间、符号）推导程序性质。

- _AOT (Ahead-of-Time) Compilation_*
预先编译为本地代码，启动无延迟，性能≈90-98% 原生。

- _Arithmetic Intensity（运算强度）_*
计算量与内存访问量的比值，决定 Roofline 模型性能上界。

- --

## 2. B {#b}

- _Baseline JIT_*
简单快速的即时编译，线性映射指令，性能≈50-70% 原生。

- _Binary Format（二进制格式）_*
紧凑的字节码表示，魔数 `00 61 73 6d`，LEB128 编码。

- _Bounds Checking（边界检查）_*
每次内存访问验证是否越界，开销≈5-10%，可优化。

- --

## 3. C {#c}

- _Capability Security（能力安全）_*
基于不可伪造句柄的访问控制，WASI 采用此模型。

- _CFI (Control Flow Integrity, 控制流完整性)_*
保证跳转目标合法，防 ROP/JOP 攻击。

- _Call Stack（调用栈）_*
函数调用的栈帧序列，Wasm 与宿主分离。

- --

## 4. D {#d}

- _Denotational Semantics（指称语义）_*
将程序映射到数学域，\( \llbracket \cdot \rrbracket : \text{Prog} \to \text{Domain} \)。

- _Determinism（确定性）_*
相同输入必产生相同输出，Wasm 通过 IEEE-754 保证浮点确定性。

- _Data Race（数据竞争）_*
并发无同步访问共享内存，Wasm 通过原子指令防御。

- --

## 5. E {#e}

- _Exception Handling（异常处理）_*
Stage 4 提案，`try/catch/throw` 结构化异常。

- _Execution Model（执行模型）_*
定义指令如何转换状态，Wasm 采用小步操作语义。

- --

## 6. F {#f}

- _Formal Semantics（形式化语义）_*
数学化定义程序行为，Wasm 有操作语义、指称语义、公理语义。

- _Function Type（函数类型）_*
签名 \( [t_1^_] \to [t_2^_] \)，多返回值已支持。

- --

## 7. G {#g}

- _GC (Garbage Collection, 垃圾回收)_*
自动内存管理，Stage 3 提案，支持 Java/Kotlin 等语言。

- _Global Variable（全局变量）_*
模块级可变/不可变变量，通过 `global.get/set` 访问。

- --

## 8. H {#h}

- _Hoare Logic（霍尔逻辑）_*
公理语义，判断形式 \( \{P\} I \{Q\} \)。

- _Host Function（宿主函数）_*
由宿主导入的函数，跨边界调用开销≈0.4-2 µs。

- --

## 9. I {#i}

- _Instruction Set（指令集）_*
MVP 178 条 + SIMD 128 条 + 线程/异常/多返回值。

- _Interface Types（接口类型）_*
提案，简化 Wasm ↔ 宿主互操作，无需手动序列化。

- --

## 10. J {#j}

- _JIT (Just-In-Time) Compilation_*
运行时编译，分 Baseline（快）和 Optimizing（慢但快速）。

- --

## 11. L {#l}

- _LEB128（小端 Base-128）_*
变长整数编码，节省空间，解码快速。

- _Linear Memory（线性内存）_*
连续字节数组，32 位默认上限 4 GB，Memory64 > 16 EB。

- _Linker（链接器）_*
组合多模块，解析导入/导出，构建最终实例。

- --

## 12. M {#m}

- _Memory Model（内存模型）_*
定义并发内存访问语义，Wasm 基于 C++11 模型。

- _Module（模块）_*
Wasm 部署单元，包含函数、内存、表、全局变量。

- --

## 13. O {#o}

- _Operational Semantics（操作语义）_*
定义状态转移规则，分小步（单步）和大步（多步）。

- _Optimizing JIT_*
高级优化编译，寄存器分配、死代码消除，性能≈85-95% 原生。

- --

## 14. P {#p}

- _Preservation（保持性）_*
类型安全定理之一，归约保持类型不变。

- _Progress（进展性）_*
类型安全定理之一，良类型表达式可继续归约或已是值。

- --

## 15. R {#r}

- _Reference Types（引用类型）_*
Stage 4 提案，`funcref / externref`，支持外部对象。

- _Roofline Model（屋顶线模型）_*
性能分析模型，\( \text{Perf} = \min(\text{Compute}, \text{Bandwidth}/\text{AI}) \)。

- --

## 16. S {#s}

- _Sandbox（沙箱）_*
隔离执行环境，内存不可越界，无宿主资源访问。

- _SIMD (Single Instruction Multiple Data)_*
128 位向量指令，加速并行计算 2-4×。

- _Stack Machine（栈式机器）_*
零地址指令，操作数栈隐式，易验证。

- _Symbolic Execution（符号执行）_*
用符号值替代具体值，探索所有路径，检测 bug。

- --

## 17. T {#t}

- _Table（表）_*
存放函数引用，用于间接调用 `call_indirect`。

- _Trap（陷阱）_*
运行时错误，立即终止，如除零、越界。

- _Type System（类型系统）_*
静态类型检查，\( i32 / i64 / f32 / f64 / v128 \)。

- --

## 18. V {#v}

- _Validation（验证）_*
静态检查模块合法性，线性时间 \( O(n) \)，保证无 UB。

- _Value Type（值类型）_*
基本数据类型，栈上操作数。

- --

## 19. W {#w}

- _WASI (WebAssembly System Interface)_*
标准系统调用接口，能力安全模型，支持文件/网络/时钟。

- _WAT (WebAssembly Text Format)_*
人类可读文本格式，S-表达式，与二进制一一对应。

- --

## 20. Z {#z}

- _Zero-Copy（零拷贝）_*
通过共享内存避免数据复制，Wasm ↔ 宿主可通过 Memory Import 实现。

- --

## 21. 符号表 {#符号表}

| 符号 | 含义 |
|------|------|
| \( \llbracket \cdot \rrbracket \) | 语义解释函数 |
| \( \vdash \) | 类型判断 |
| \( \rightarrow \) | 单步转移 |
| \( \xrightarrow{_} \) | 多步转移（传递闭包） |
| \( \implies \) | 逻辑蕴含 |
| \( \equiv \) | 语义等价 |
| \( \sqsubseteq \) | 偏序（抽象解释） |
| \( \nabla \) | Widening 算子 |
| \( \mu \) | 最小不动点算子 |
| \( O(\cdot) \) | 算法复杂度 |
| \( \bot \) | 底元素 / trap |
| \( \top \) | 顶元素 / unknown |

- --

## 22. 缩略语 {#缩略语}

| 缩略语 | 全称 |
|--------|------|
| AOT | Ahead-of-Time |
| AST | Abstract Syntax Tree |
| CFI | Control Flow Integrity |
| DOP | Data-Oriented Programming |
| JIT | Just-In-Time |
| JOP | Jump-Oriented Programming |
| LEB128 | Little Endian Base-128 |
| MVP | Minimum Viable Product |
| ROP | Return-Oriented Programming |
| SAT | Satisfiability |
| SIMD | Single Instruction Multiple Data |
| SMT | Satisfiability Modulo Theories |
| UAF | Use-After-Free |
| UB | Undefined Behavior |
| WASI | WebAssembly System Interface |
| WAT | WebAssembly Text Format |
| WCET | Worst-Case Execution Time |

- --

- _使用说明_*：

- **形式化术语**：附带数学定义
- **工程术语**：附带性能数据
- **批判性术语**：附带限制说明

_本术语表采用批判性视角，不仅定义术语，更揭示其边界与权衡。_


---

## 关联网络

### 前向引用

> 本文档为以下文档提供基础：
>
> - [相关文档](./README.md) (待补充)

### 后向引用

> 本文档依赖以下基础文档：
>
> - [基础文档](./README.md) (待补充)

### 交叉链接

> 相关主题：
>
> - [主题A](./README.md) (待补充)
> - [主题B](./README.md) (待补充)

---

_本文档由 FormalScience 文档规范化工具自动生成_
