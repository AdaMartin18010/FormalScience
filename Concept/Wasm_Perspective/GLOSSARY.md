# WebAssembly 术语表 (GLOSSARY)

## 📋 目录

- [1 A](#1-a)
- [2 B](#2-b)
- [3 C](#3-c)
- [4 D](#4-d)
- [5 E](#5-e)
- [6 F](#6-f)
- [7 G](#7-g)
- [8 H](#8-h)
- [9 I](#9-i)
- [10 J](#10-j)
- [11 L](#11-l)
- [12 M](#12-m)
- [13 O](#13-o)
- [14 P](#14-p)
- [15 R](#15-r)
- [16 S](#16-s)
- [17 T](#17-t)
- [18 V](#18-v)
- [19 W](#19-w)
- [20 Z](#20-z)
- [21 符号表](#21-符号表)
- [22 缩略语](#22-缩略语)

---

## 1 A

**Abstract Machine（抽象机器）**
形式化的计算模型，定义状态空间与转移关系。Wasm 抽象机器 = 栈 + 内存 + 表 + 全局变量。

**Abstract Interpretation（抽象解释）**
静态分析技术，通过抽象域（如区间、符号）推导程序性质。

**AOT (Ahead-of-Time) Compilation**
预先编译为本地代码，启动无延迟，性能≈90-98% 原生。

**Arithmetic Intensity（运算强度）**
计算量与内存访问量的比值，决定 Roofline 模型性能上界。

---

## 2 B

**Baseline JIT**
简单快速的即时编译，线性映射指令，性能≈50-70% 原生。

**Binary Format（二进制格式）**
紧凑的字节码表示，魔数 `00 61 73 6d`，LEB128 编码。

**Bounds Checking（边界检查）**
每次内存访问验证是否越界，开销≈5-10%，可优化。

---

## 3 C

**Capability Security（能力安全）**
基于不可伪造句柄的访问控制，WASI 采用此模型。

**CFI (Control Flow Integrity, 控制流完整性)**
保证跳转目标合法，防 ROP/JOP 攻击。

**Call Stack（调用栈）**
函数调用的栈帧序列，Wasm 与宿主分离。

---

## 4 D

**Denotational Semantics（指称语义）**
将程序映射到数学域，\( \llbracket \cdot \rrbracket : \text{Prog} \to \text{Domain} \)。

**Determinism（确定性）**
相同输入必产生相同输出，Wasm 通过 IEEE-754 保证浮点确定性。

**Data Race（数据竞争）**
并发无同步访问共享内存，Wasm 通过原子指令防御。

---

## 5 E

**Exception Handling（异常处理）**
Stage 4 提案，`try/catch/throw` 结构化异常。

**Execution Model（执行模型）**
定义指令如何转换状态，Wasm 采用小步操作语义。

---

## 6 F

**Formal Semantics（形式化语义）**
数学化定义程序行为，Wasm 有操作语义、指称语义、公理语义。

**Function Type（函数类型）**
签名 \( [t_1^_] \to [t_2^_] \)，多返回值已支持。

---

## 7 G

**GC (Garbage Collection, 垃圾回收)**
自动内存管理，Stage 3 提案，支持 Java/Kotlin 等语言。

**Global Variable（全局变量）**
模块级可变/不可变变量，通过 `global.get/set` 访问。

---

## 8 H

**Hoare Logic（霍尔逻辑）**
公理语义，判断形式 \( \{P\} I \{Q\} \)。

**Host Function（宿主函数）**
由宿主导入的函数，跨边界调用开销≈0.4-2 µs。

---

## 9 I

**Instruction Set（指令集）**
MVP 178 条 + SIMD 128 条 + 线程/异常/多返回值。

**Interface Types（接口类型）**
提案，简化 Wasm ↔ 宿主互操作，无需手动序列化。

---

## 10 J

**JIT (Just-In-Time) Compilation**
运行时编译，分 Baseline（快）和 Optimizing（慢但快速）。

---

## 11 L

**LEB128（小端 Base-128）**
变长整数编码，节省空间，解码快速。

**Linear Memory（线性内存）**
连续字节数组，32 位默认上限 4 GB，Memory64 > 16 EB。

**Linker（链接器）**
组合多模块，解析导入/导出，构建最终实例。

---

## 12 M

**Memory Model（内存模型）**
定义并发内存访问语义，Wasm 基于 C++11 模型。

**Module（模块）**
Wasm 部署单元，包含函数、内存、表、全局变量。

---

## 13 O

**Operational Semantics（操作语义）**
定义状态转移规则，分小步（单步）和大步（多步）。

**Optimizing JIT**
高级优化编译，寄存器分配、死代码消除，性能≈85-95% 原生。

---

## 14 P

**Preservation（保持性）**
类型安全定理之一，归约保持类型不变。

**Progress（进展性）**
类型安全定理之一，良类型表达式可继续归约或已是值。

---

## 15 R

**Reference Types（引用类型）**
Stage 4 提案，`funcref / externref`，支持外部对象。

**Roofline Model（屋顶线模型）**
性能分析模型，\( \text{Perf} = \min(\text{Compute}, \text{Bandwidth}/\text{AI}) \)。

---

## 16 S

**Sandbox（沙箱）**
隔离执行环境，内存不可越界，无宿主资源访问。

**SIMD (Single Instruction Multiple Data)**
128 位向量指令，加速并行计算 2-4×。

**Stack Machine（栈式机器）**
零地址指令，操作数栈隐式，易验证。

**Symbolic Execution（符号执行）**
用符号值替代具体值，探索所有路径，检测 bug。

---

## 17 T

**Table（表）**
存放函数引用，用于间接调用 `call_indirect`。

**Trap（陷阱）**
运行时错误，立即终止，如除零、越界。

**Type System（类型系统）**
静态类型检查，\( i32 / i64 / f32 / f64 / v128 \)。

---

## 18 V

**Validation（验证）**
静态检查模块合法性，线性时间 \( O(n) \)，保证无 UB。

**Value Type（值类型）**
基本数据类型，栈上操作数。

---

## 19 W

**WASI (WebAssembly System Interface)**
标准系统调用接口，能力安全模型，支持文件/网络/时钟。

**WAT (WebAssembly Text Format)**
人类可读文本格式，S-表达式，与二进制一一对应。

---

## 20 Z

**Zero-Copy（零拷贝）**
通过共享内存避免数据复制，Wasm ↔ 宿主可通过 Memory Import 实现。

---

## 21 符号表

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

---

## 22 缩略语

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

---

**使用说明**：

- **形式化术语**：附带数学定义
- **工程术语**：附带性能数据
- **批判性术语**：附带限制说明

_本术语表采用批判性视角，不仅定义术语，更揭示其边界与权衡。_
