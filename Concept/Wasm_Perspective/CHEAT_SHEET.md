# WebAssembly 快速参考卡

**版本**：1.0.0
**最后更新**：2025-10-30
**打印友好** ✓

---

## 🚀 快速开始（5 分钟）

```bash
# 安装 Rust 工具链
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
rustup target add wasm32-wasi

# 创建项目
cargo new --lib my_wasm && cd my_wasm

# 编译
cargo build --release --target wasm32-wasi

# 运行
wasmedge target/wasm32-wasi/release/my_wasm.wasm
```

---

## 📦 核心指令速查

### 整数运算

| 指令 | 功能 | 栈行为 |
|------|------|--------|
| `i32.add` | 加法 | [i32 i32] → [i32] |
| `i32.sub` | 减法 | [i32 i32] → [i32] |
| `i32.mul` | 乘法 | [i32 i32] → [i32] |
| `i32.div_s` | 有符号除 | [i32 i32] → [i32] |
| `i32.rem_u` | 无符号取模 | [i32 i32] → [i32] |
| `i32.and` | 位与 | [i32 i32] → [i32] |
| `i32.or` | 位或 | [i32 i32] → [i32] |
| `i32.shl` | 左移 | [i32 i32] → [i32] |

### 浮点运算

| 指令 | 功能 | 栈行为 |
|------|------|--------|
| `f32.add` | 加法 | [f32 f32] → [f32] |
| `f32.div` | 除法 | [f32 f32] → [f32] |
| `f32.sqrt` | 平方根 | [f32] → [f32] |
| `f32.min` | 最小值 | [f32 f32] → [f32] |
| `f32.max` | 最大值 | [f32 f32] → [f32] |

### 内存操作

| 指令 | 功能 | 说明 |
|------|------|------|
| `i32.load` | 读取 32 位 | `(i32.load offset align)` |
| `i32.store` | 写入 32 位 | `(i32.store offset align)` |
| `memory.size` | 获取页数 | 1 页 = 64 KB |
| `memory.grow` | 扩展内存 | 返回旧页数或 -1 |

### 控制流

| 指令 | 功能 | 示例 |
|------|------|------|
| `block` | 代码块 | `(block (result i32) ...)` |
| `loop` | 循环 | `(loop $loop ...)` |
| `if` | 条件分支 | `(if (result i32) ...)` |
| `br` | 跳转 | `(br $label)` |
| `br_if` | 条件跳转 | `(br_if $label)` |
| `return` | 返回 | `(return)` |

---

## 🔧 编译选项速查

### Rust → Wasm

```toml
# Cargo.toml 优化配置
[profile.release]
opt-level = "z"       # 体积优化（也可用 3 = 速度）
lto = true            # 链接时优化
codegen-units = 1     # 单编译单元
panic = "abort"       # 减小体积
strip = true          # 去除符号

# SIMD 支持
[profile.release.package."*"]
opt-level = 3
```

```bash
# 编译命令
cargo build --release --target wasm32-wasi

# 启用 SIMD
RUSTFLAGS="-C target-feature=+simd128" \
  cargo build --release --target wasm32-unknown-unknown

# 生成调试信息
cargo build --target wasm32-wasi -Cdebuginfo=2

# wasm-opt 优化
wasm-opt -Oz input.wasm -o output.wasm  # 体积
wasm-opt -O3 input.wasm -o output.wasm  # 速度
```

### C/C++ → Wasm

```bash
# Emscripten 基础
emcc hello.c -o hello.wasm

# 优化编译
emcc hello.c -O3 -s WASM=1 \
  -s EXPORTED_FUNCTIONS='["_main"]' \
  -o hello.wasm

# SIMD 支持
emcc hello.c -O3 -msimd128 -o hello.wasm
```

---

## 🎯 性能优化速查

### 延迟参考（WasmEdge, x86_64 3.4 GHz）

| 操作 | 延迟 | 说明 |
|------|------|------|
| **冷启动** | 2.5 µs | 加载到首次执行 |
| **热启动** | 0.1 µs | 实例已存在 |
| **跨边界调用** | 0.4-2 µs | Wasm ↔ 宿主 |
| **i32.add** | 1 cycle | ~0.3 ns |
| **f64.div** | 4-13 cycles | ~1-4 ns |
| **memory.grow** | 1-10 µs | 依赖大小 |

### 性能优化清单

```text
✓ 使用 AOT 编译         → +30-50% 吞吐
✓ 启用 SIMD            → +3-8× (适用场景)
✓ 批量跨边界调用        → +100-1000×
✓ 使用共享内存          → 消除拷贝
✓ wasm-opt -Oz         → -30-50% 体积
✓ 预分配内存            → 减少 realloc
✓ 对象池（热路径）      → 减少分配开销
```

---

## 🔒 安全速查

### 常见威胁

| 威胁 | Wasm 防御 | 额外措施 |
|------|----------|---------|
| **越界访问** | ✅ trap | 验证输入 |
| **类型混淆** | ✅ 类型检查 | 静态分析 |
| **栈溢出** | ✅ 调用栈隔离 | 限制递归深度 |
| **Spectre** | ❌ 无防御 | 进程隔离 + CPU 补丁 |
| **侧信道** | ❌ 无防御 | 常量时间算法 |

### 安全检查清单

```text
✓ 验证所有输入边界
✓ 使用常量时间算法（密码学）
✓ 最小化 WASI 权限
✓ 不在 Wasm 中硬编码密钥
✓ 启用 overflow-checks
✓ 定期审计依赖
✓ 启用 CSP 头
```

---

## 📐 内存模型速查

### 线性内存布局

```text
0x00000000  ┌─────────────────┐
            │   Stack         │  栈（由编译器管理）
            ├─────────────────┤
            │   Globals       │  全局变量
            ├─────────────────┤
            │   Heap          │  堆（动态分配）
            │   ↓             │
            │   ...           │
            │   ↑             │
0xFFFFFFFF  └─────────────────┘  32 位地址空间 (4 GB)
```

### 内存操作

```wat
;; 分配内存
(memory 1)              ;; 初始 1 页 (64 KB)
(memory 1 10)           ;; 初始 1 页，最大 10 页

;; 读写
(i32.store (i32.const 0) (i32.const 42))  ;; 地址 0 写入 42
(i32.load (i32.const 0))                   ;; 读取地址 0

;; 扩展
(memory.grow (i32.const 1))  ;; 扩展 1 页
```

---

## 🔄 跨边界通信速查

### JavaScript ↔ Wasm

```javascript
// 实例化
const { instance } = await WebAssembly.instantiateStreaming(
    fetch('app.wasm')
);

// 调用导出函数
const result = instance.exports.add(3, 4);

// 访问内存
const memory = instance.exports.memory;
const buffer = new Uint8Array(memory.buffer);

// 共享内存（多线程）
const memory = new WebAssembly.Memory({
    initial: 1,
    maximum: 10,
    shared: true
});
```

### Rust ↔ JavaScript

```rust
use wasm_bindgen::prelude::*;

// 导出到 JS
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 导入 JS 函数
#[wasm_bindgen]
extern "C" {
    fn alert(s: &str);
}

// 使用
#[wasm_bindgen]
pub fn greet(name: &str) {
    alert(&format!("Hello, {}!", name));
}
```

---

## 🛠️ 工具链速查

### 必备工具

```bash
# Rust 工具链
rustup target add wasm32-wasi
cargo install wasm-pack

# Emscripten (C/C++)
git clone https://github.com/emscripten-core/emsdk.git
cd emsdk && ./emsdk install latest

# WABT（工具集）
apt-get install wabt   # Debian/Ubuntu
brew install wabt      # macOS

# wasm-opt
npm install -g binaryen

# WasmEdge 运行时
curl -sSf https://raw.githubusercontent.com/WasmEdge/WasmEdge/master/utils/install.sh | bash
```

### 常用命令

```bash
# WAT ↔ Wasm 转换
wat2wasm input.wat -o output.wasm
wasm2wat input.wasm -o output.wat

# 查看模块信息
wasm-objdump -x module.wasm

# 反汇编
wasm-objdump -d module.wasm

# 验证模块
wasm-validate module.wasm

# 运行
wasmedge module.wasm
wasmtime module.wasm
```

---

## 🐛 调试速查

### Chrome DevTools

```text
1. 打开 DevTools (F12)
2. Sources → Wasm 模块自动出现
3. 设置断点（如果有 Source Map）
4. 单步调试（Step Into/Over/Out）
```

### 日志注入

```rust
// 宿主函数声明
#[link(wasm_import_module = "env")]
extern "C" {
    fn log(ptr: *const u8, len: usize);
}

// 宏封装
macro_rules! debug {
    ($($arg:tt)*) => {{
        let s = format!($($arg)*);
        unsafe {
            log(s.as_ptr(), s.len());
        }
    }};
}

// 使用
debug!("Value: {}", x);
```

---

## 📊 性能分析速查

### 浏览器 Profiling

```javascript
// 测量时间
console.time('wasm_execution');
instance.exports.heavy_computation();
console.timeEnd('wasm_execution');

// Performance API
const start = performance.now();
instance.exports.heavy_computation();
const duration = performance.now() - start;
console.log(`${duration}ms`);
```

### 命令行 Profiling

```bash
# Linux perf
perf record -F 99 -g wasmedge app.wasm
perf script | flamegraph.pl > flame.svg

# 内存分析
valgrind --tool=massif wasmedge app.wasm
ms_print massif.out.*
```

---

## 🔢 常见数值速查

| 概念 | 值 | 说明 |
|------|-----|------|
| **页大小** | 64 KB | 线性内存单位 |
| **默认地址空间** | 4 GB | 32 位指针 |
| **Memory64 地址空间** | 16 EB | 64 位指针 |
| **栈大小** | ~1 MB | 编译器决定 |
| **指令数（MVP）** | 178 | 核心指令集 |
| **指令数（全部）** | ~387 | 含提案 |

---

## 🌐 浏览器兼容性速查

| 特性 | Chrome | Firefox | Safari | Edge |
|------|--------|---------|--------|------|
| **Core MVP** | ✅ 57+ | ✅ 52+ | ✅ 11+ | ✅ 79+ |
| **SIMD** | ✅ 91+ | ✅ 89+ | ⚠️ 16.4+ | ✅ 91+ |
| **Threads** | ✅ 74+ | ✅ 79+ | ⚠️ 15.2+ | ✅ 79+ |
| **Exception** | ✅ 95+ | 🚧 | 🚧 | ✅ 95+ |
| **Memory64** | 🚧 | 🚧 | 🚧 | 🚧 |

**图例**：✅ 支持，⚠️ 部分支持，🚧 实验性

---

## 📖 术语速查

| 术语 | 含义 | 示例 |
|------|------|------|
| **线性内存** | 连续字节数组 | 64 KB 页 |
| **trap** | 运行时错误 | 越界访问 |
| **宿主函数** | 外部函数 | JS API |
| **WASI** | 系统接口 | 文件/网络 |
| **AOT** | 提前编译 | wasmedgec |
| **JIT** | 即时编译 | V8 |
| **MVP** | 最小产品 | 核心功能集 |

---

## 🔗 快速链接

| 资源 | 链接 |
|------|------|
| **规范** | [webassembly.github.io/spec](https://webassembly.github.io/spec/) |
| **WASI** | [github.com/WebAssembly/WASI](https://github.com/WebAssembly/WASI) |
| **Rust Book** | [rustwasm.github.io/docs/book](https://rustwasm.github.io/docs/book/) |
| **MDN** | [developer.mozilla.org/WebAssembly](https://developer.mozilla.org/en-US/docs/WebAssembly) |
| **WasmEdge** | [wasmedge.org](https://wasmedge.org/) |

---

## 💡 快速诊断

### 问题：Wasm 加载失败

```text
✓ 检查 MIME 类型（application/wasm）
✓ 检查 CORS 头
✓ 验证模块：wasm-validate module.wasm
✓ 查看浏览器控制台错误
```

### 问题：性能不如预期

```text
✓ 是否使用 AOT 编译？
✓ 是否启用优化？（-O3 或 -Oz）
✓ 是否频繁跨边界？（改批量调用）
✓ 是否启用 SIMD？（适用场景）
✓ Profile 找热点
```

### 问题：内存不足

```text
✓ 当前使用多少？（memory.size）
✓ 是否有泄漏？（监控增长）
✓ 是否可分块处理？
✓ 是否需要 Memory64？（>4 GB）
```

---

**打印提示**：

- A4 双面打印
- 建议彩色（语法高亮）
- 可缩放到 80%（更紧凑）

**版本**：1.0.0 | **更新**：2025-10-30 | **许可证**：CC BY-SA 4.0
