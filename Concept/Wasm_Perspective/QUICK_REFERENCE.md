# WebAssembly 快速参考 (Quick Reference)

## 核心命题速查

### 确定性
\[
\forall M, S : \llbracket M \rrbracket(S) \text{ 唯一确定}
\]

### 类型安全
\[
\text{Validate}(M) \implies \text{Progress}(M) \wedge \text{Preservation}(M)
\]

### 验证复杂度
\[
T(\text{Validate}) = O(|M|)
\]

### 性能界限
\[
\text{Perf}_{\text{wasm}} \in [0.85, 0.95] \times \text{Perf}_{\text{native}}
\]

### 沙箱隔离
\[
\text{LinearMemory}_{\text{wasm}} \cap \text{HostMemory} = \emptyset
\]

---

## 类型系统速查

### 值类型
```
i32 | i64 | f32 | f64 | v128
```

### 函数类型
```
[t1*] -> [t2*]  // 多返回值已支持
```

### 类型判断
\[
C \vdash I : [t_1^*] \to [t_2^*]
\]

---

## 指令集速查

### 算术指令
```
i32.add    [i32 i32] -> [i32]
i32.mul    [i32 i32] -> [i32]
i32.div_s  [i32 i32] -> [i32]  // 除零 trap
f32.sqrt   [f32] -> [f32]
```

### 控制流
```
block [t*] ... end       [] -> [t*]
loop [t*] ... end        [] -> [t*]
if [t*] ... else ... end [i32] -> [t*]
br i                     [t1*, t*] -> [t2*]
call x                   [t1*] -> [t2*]
```

### 内存指令
```
i32.load     [i32] -> [i32]
i32.store    [i32 i32] -> []
memory.size  [] -> [i32]
memory.grow  [i32] -> [i32]
```

### SIMD 指令
```
i32x4.add    [v128 v128] -> [v128]
f32x4.mul    [v128 v128] -> [v128]
i8x16.splat  [i32] -> [v128]
```

---

## 性能数据速查

### 编译策略
| 策略 | 启动 | 吞吐 |
|------|------|------|
| 解释器 | <1 ms | 1-10% |
| Baseline JIT | 5-10 ms | 50-70% |
| Optimizing JIT | 30-100 ms | 85-95% |
| AOT | 0 ms | 90-98% |

### 指令延迟（Skylake, cycles）
| 指令 | 延迟 | 吞吐/周期 |
|------|------|----------|
| i32.add | 1 | 4 |
| i32.mul | 3 | 1 |
| f64.div | 4-13 | 1 |
| memory.load | 3-200 | 取决缓存 |

### 开销
```
验证：1-2 ms/MB
边界检查：5-10%
栈→寄存器：5-10%
总抽象税：5-15%
```

---

## 安全性速查

### 已防御
- ✅ 栈溢出 / ROP / JOP
- ✅ 堆溢出（边界检查）
- ✅ UAF（无指针）
- ✅ 类型混淆（运行时检查）

### 未完全防御
- ⚠️ Spectre（推测执行泄漏）
- ⚠️ 侧信道（时序泄漏）
- ⚠️ DoS（资源耗尽）
- ⚠️ 实现漏洞（JIT 编译器）

---

## 应用场景速查

### 强适配
- Serverless（冷启动 <5 ms）
- 边缘 AI（GPU 加速）
- IoT（差分 KB 级）
- 区块链（确定性）
- 插件系统（沙箱）

### 不适配
- DOM 密集操作
- 大堆（>4 GB，Memory64 改善中）
- 动态代码生成

---

## 命令速查

### 编译
```bash
# C/C++
emcc -O3 -s WASM=1 code.c -o code.wasm

# Rust
cargo build --target wasm32-wasi --release

# WAT -> WASM
wat2wasm code.wat -o code.wasm

# WASM -> WAT
wasm2wat code.wasm -o code.wat
```

### 运行
```bash
# Node.js
node --experimental-wasm-modules code.wasm

# WasmEdge
wasmedge code.wasm

# AOT 预编译
wasmedgec code.wasm code.so
wasmedge code.so
```

### 分析
```bash
# 反汇编
wasm-objdump -d code.wasm

# 验证
wasm-validate code.wasm

# 优化
wasm-opt -O3 code.wasm -o optimized.wasm
```

---

## 关键公式速查

### ROI 模型
\[
\text{Savings} = \sum (\Delta \text{Traffic} + \Delta \text{Memory} + \Delta \text{DevOps})
\]

### 盈亏平衡点
```
6 个月（基于 10k 边缘节点）
```

### 成本函数
\[
C_{\text{total}} = C_{\text{compute}} + C_{\text{network}} + C_{\text{storage}} + C_{\text{devops}}
\]

### 加速比
\[
\text{Speedup}_{\text{SIMD}} \approx \frac{\text{lanes}}{1.2} \approx 3-12×
\]

---

## 工具链速查

### 运行时
- WasmEdge（边缘优化）
- Wasmtime（功能完整）
- Wasmer（商业友好）
- WAMR（超轻量 <100 KB）

### 编译器
- Emscripten（C/C++）
- wasm-pack（Rust）
- AssemblyScript（TypeScript-like）
- TinyGo（Go 子集）

### 验证工具
- Isabelle/Wasm（定理证明）
- Wasm-Coq（Coq 机械化）
- K-Wasm（可执行语义）

---

## 常见陷阱速查

### 除零
```wasm
i32.const 0
i32.div_s  ;; trap!
```

### 越界
```wasm
i32.const 0xFFFFFFFF
i32.load   ;; trap!
```

### 类型不匹配
```wasm
(call_indirect (type $sig) (i32.const 0))
;; 若 table[0] 类型≠$sig，则 trap!
```

### 整数溢出
```wasm
i32.const 0x80000000  ;; INT_MIN
i32.const -1
i32.div_s             ;; trap!
```

---

## 优化技巧速查

### 编译器优化
```rust
// 启用 LTO
[profile.release]
lto = true

// 启用 SIMD
#[target_feature(enable = "simd128")]
```

### 算法优化
1. 减少边界检查（循环外提）
2. 内存对齐（64 字节）
3. 避免间接调用
4. SIMD 向量化

### 部署优化
- AOT 预编译（启动最快）
- 差分更新（流量最省）
- 多实例池化（密度最高）

---

## 批判性检查清单

### 性能预期
- ❓ 是否高估了性能？（抽象税 5-15%）
- ❓ 是否忽略了 JIT 预热？
- ❓ 是否考虑了内存访问模式？

### 安全预期
- ❓ 是否认为沙箱绝对安全？（Spectre 未防御）
- ❓ 是否依赖形式化验证？（实现仍可能有漏洞）
- ❓ 是否考虑了侧信道？（时序泄漏）

### 生态预期
- ❓ 是否高估了工具链成熟度？
- ❓ 是否忽略了 JS 互操作开销？
- ❓ 是否考虑了路径依赖？（JS 霸权）

---

## 延伸阅读

### 理论
- 01_Foundational_Theory（形式化语义、类型系统）
- 06_Philosophical_Foundations（可移植性理论）

### 实践
- 03_Runtime_Systems（编译策略）
- 04_System_Integration（WASI、内存共享）
- 05_Application_Patterns（Serverless、IoT）

### 批判
- 各章节"批判性分析"
- FAQ Q19-Q22

---

**使用建议**：
- 开发时：对照指令集和类型规则
- 优化时：参考性能数据和优化技巧
- 决策时：检查批判性清单

*本快速参考旨在提供"即查即用"的关键信息，同时保持批判性视角。*
