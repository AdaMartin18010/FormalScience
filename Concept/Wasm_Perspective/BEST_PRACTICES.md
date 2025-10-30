# WebAssembly 最佳实践与常见陷阱

**版本**：1.0.0
**最后更新**：2025-10-30
**适用对象**：开发工程师、架构师

---

## 概述

本文档总结了 WebAssembly 开发中的最佳实践、常见陷阱和优化技巧，基于真实生产环境的经验教训。

---

## 📋 目录

1. [性能优化最佳实践](#性能优化最佳实践)
2. [安全最佳实践](#安全最佳实践)
3. [内存管理最佳实践](#内存管理最佳实践)
4. [跨边界通信最佳实践](#跨边界通信最佳实践)
5. [工具链最佳实践](#工具链最佳实践)
6. [常见陷阱与解决方案](#常见陷阱与解决方案)
7. [调试最佳实践](#调试最佳实践)
8. [部署最佳实践](#部署最佳实践)

---

## 性能优化最佳实践

### ✅ DO（推荐做法）

#### 1. 使用 AOT 编译用于生产环境

```bash
# WasmEdge AOT 编译
wasmedgec app.wasm app.so

# 性能提升：30-50%
# 启动时间：降低 80%
```

**原因**：

- 消除运行时编译开销
- 更好的代码优化
- 冷启动时间显著降低

#### 2. 启用 SIMD 优化

```rust
// Cargo.toml
[profile.release]
opt-level = 3

// 编译时
RUSTFLAGS="-C target-feature=+simd128" cargo build --release --target wasm32-wasi
```

**适用场景**：

- 图像/视频处理
- 音频 DSP
- 数值计算
- AI 推理

**性能提升**：3-8× (取决于算法)

#### 3. 批量跨边界调用

❌ **错误示例**（频繁调用）：

```javascript
// BAD: 每个像素都跨边界
for (let i = 0; i < pixels.length; i++) {
    pixels[i] = wasmModule.processPixel(pixels[i]);
}
// 开销：0.4 µs × 1M pixels = 400 ms
```

✅ **正确示例**（批量处理）：

```javascript
// GOOD: 批量传递
const processedPixels = wasmModule.processPixelBatch(pixels);
// 开销：0.4 µs × 1 = 0.4 µs
```

**性能提升**：100-1000×

#### 4. 使用共享内存而非消息传递

```javascript
// GOOD: 零拷贝
const memory = new WebAssembly.Memory({ initial: 10, shared: true });
const view = new Uint8Array(memory.buffer);
// Wasm 直接读写 view
```

**vs**

```javascript
// BAD: 多次拷贝
postMessage(data); // 拷贝 1
// Worker 接收 // 拷贝 2
```

#### 5. 预分配内存

```rust
// GOOD: 预分配
let mut buffer = Vec::with_capacity(1000000);

// vs

// BAD: 多次重分配
let mut buffer = Vec::new();
for i in 0..1000000 {
    buffer.push(i); // 多次 realloc
}
```

#### 6. 使用 wasm-opt 优化

```bash
# 体积优化（-Oz）
wasm-opt -Oz input.wasm -o output.wasm
# 体积减少：30-50%

# 速度优化（-O3）
wasm-opt -O3 input.wasm -o output.wasm
# 性能提升：10-20%
```

### ❌ DON'T（避免做法）

#### 1. 避免频繁的小内存分配

```rust
// BAD: 每次迭代分配
for _ in 0..1000 {
    let s = String::from("temp"); // 1000 次分配
}

// GOOD: 复用缓冲区
let mut s = String::with_capacity(100);
for _ in 0..1000 {
    s.clear();
    s.push_str("temp");
}
```

#### 2. 避免未对齐的内存访问

```rust
// BAD: 可能未对齐
let ptr = buffer.as_ptr() as *const u32;
let value = unsafe { *ptr }; // 可能 trap

// GOOD: 显式对齐
let aligned = buffer.as_ptr().align_offset(4);
let ptr = unsafe { buffer.as_ptr().add(aligned) as *const u32 };
```

#### 3. 避免过度使用 call_indirect

```wat
;; BAD: 间接调用开销 2-3×
(call_indirect (type $sig) (i32.const 0))

;; GOOD: 直接调用（如果可能）
(call $function_name)
```

---

## 安全最佳实践

### ✅ DO（推荐做法）

#### 1. 验证所有输入

```rust
#[no_mangle]
pub extern "C" fn process_data(ptr: *const u8, len: usize) -> i32 {
    // GOOD: 验证边界
    if len > MAX_SIZE {
        return -1; // 错误码
    }

    // GOOD: 使用安全抽象
    let slice = unsafe {
        std::slice::from_raw_parts(ptr, len)
    };

    // 处理...
    0
}
```

#### 2. 使用常量时间算法（密码学）

```rust
// GOOD: 常量时间比较
pub fn secure_compare(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }

    let mut result = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        result |= x ^ y;
    }
    result == 0
}

// BAD: 提前返回（时序泄漏）
pub fn insecure_compare(a: &[u8], b: &[u8]) -> bool {
    for (x, y) in a.iter().zip(b.iter()) {
        if x != y {
            return false; // 泄漏位置信息
        }
    }
    true
}
```

#### 3. 最小化 WASI 权限

```bash
# GOOD: 只授予必要权限
wasmedge --dir=/tmp/data::/data app.wasm

# BAD: 授予整个文件系统
wasmedge --dir=/:/ app.wasm
```

#### 4. 启用内存保护

```toml
# Cargo.toml
[profile.release]
overflow-checks = true
```

### ❌ DON'T（避免做法）

#### 1. 避免信任用户输入

```rust
// BAD: 直接使用用户输入作为索引
let index = user_input;
buffer[index] // 可能越界

// GOOD: 验证范围
let index = user_input.min(buffer.len() - 1);
buffer[index]
```

#### 2. 避免在 Wasm 中存储密钥

```rust
// BAD: 硬编码密钥
const API_KEY: &str = "secret123";

// GOOD: 通过宿主函数获取
extern "C" {
    fn get_api_key(buf: *mut u8, len: usize) -> i32;
}
```

---

## 内存管理最佳实践

### ✅ DO（推荐做法）

#### 1. 使用对象池

```rust
pub struct ObjectPool<T> {
    objects: Vec<T>,
    available: Vec<usize>,
}

impl<T: Default> ObjectPool<T> {
    pub fn acquire(&mut self) -> Option<&mut T> {
        self.available.pop()
            .map(|idx| &mut self.objects[idx])
    }

    pub fn release(&mut self, idx: usize) {
        self.available.push(idx);
    }
}
```

#### 2. 监控内存增长

```rust
#[no_mangle]
pub extern "C" fn get_memory_usage() -> usize {
    // Wasm 线性内存页数
    core::arch::wasm32::memory_size(0) * 65536
}
```

#### 3. 及时释放大对象

```rust
// GOOD: 显式释放
{
    let large_buffer = vec![0u8; 100_000_000];
    process(&large_buffer);
} // large_buffer 立即释放

// BAD: 持有引用过久
let large_buffer = vec![0u8; 100_000_000];
// ... 其他代码 ...
process(&large_buffer);
```

### ❌ DON'T（避免做法）

#### 1. 避免内存泄漏

```rust
// BAD: 忘记释放 Box
let ptr = Box::into_raw(Box::new(data));
// ... 忘记 drop

// GOOD: 确保释放
let ptr = Box::into_raw(Box::new(data));
// 使用完后
unsafe { drop(Box::from_raw(ptr)); }
```

#### 2. 避免循环引用

```rust
use std::rc::Rc;
use std::cell::RefCell;

// BAD: 循环引用导致内存泄漏
struct Node {
    next: Option<Rc<RefCell<Node>>>,
    prev: Option<Rc<RefCell<Node>>>, // 循环引用
}

// GOOD: 使用 Weak 打破循环
use std::rc::Weak;

struct Node {
    next: Option<Rc<RefCell<Node>>>,
    prev: Option<Weak<RefCell<Node>>>, // 弱引用
}
```

---

## 跨边界通信最佳实践

### ✅ DO（推荐做法）

#### 1. 使用类型化数组

```javascript
// GOOD: 零拷贝视图
const memory = wasmInstance.exports.memory;
const buffer = new Uint8Array(memory.buffer, ptr, len);
```

#### 2. 传递指针而非值

```rust
// GOOD: 传递指针
#[no_mangle]
pub extern "C" fn process(data: *const u8, len: usize) -> i32 {
    // ...
}
```

#### 3. 使用 Interface Types（提案）

```wit
// 未来：高效类型传递
interface image-processor {
    process: func(image: list<u8>) -> list<u8>
}
```

### ❌ DON'T（避免做法）

#### 1. 避免传递复杂 JS 对象

```javascript
// BAD: 需要序列化
wasmModule.process(JSON.stringify(complexObject));

// GOOD: 传递扁平数据
wasmModule.process(id, value1, value2);
```

---

## 工具链最佳实践

### ✅ DO（推荐做法）

#### 1. 使用统一的优化配置

```toml
# Cargo.toml
[profile.release]
opt-level = "z"        # 体积优化
lto = true             # 链接时优化
codegen-units = 1      # 单个编译单元
panic = "abort"        # 减小体积
strip = true           # 去除符号
```

#### 2. 启用调试信息（开发环境）

```toml
[profile.dev]
debug = 2              # 完整调试信息

[profile.release]
debug = 1              # 行号信息
```

#### 3. 使用 CI/CD 自动化

```yaml
# .github/workflows/wasm.yml
name: Build Wasm
on: [push]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Build
        run: |
          cargo build --release --target wasm32-wasi
          wasm-opt -Oz target/wasm32-wasi/release/*.wasm -o optimized.wasm
      - name: Test size
        run: |
          size=$(stat -c%s optimized.wasm)
          if [ $size -gt 1000000 ]; then
            echo "Wasm too large: $size bytes"
            exit 1
          fi
```

---

## 常见陷阱与解决方案

### 陷阱 1：内存 4GB 限制

**问题**：

```rust
// 尝试分配 5GB
let huge = vec![0u8; 5_000_000_000]; // panic!
```

**解决方案**：

```rust
// 1. 使用 Memory64（提案）
// 2. 分块处理
const CHUNK_SIZE: usize = 100_000_000;
for chunk in data.chunks(CHUNK_SIZE) {
    process_chunk(chunk);
}
```

### 陷阱 2：浮点不确定性

**问题**：

```rust
// 不同平台可能不同
let result = 0.1 + 0.2; // 可能不等于 0.3
```

**解决方案**：

```rust
// 使用整数运算
let result = (10 + 20) / 100; // 确定性
```

### 陷阱 3：栈溢出

**问题**：

```rust
// 递归过深
fn factorial(n: u64) -> u64 {
    if n == 0 { 1 } else { n * factorial(n - 1) }
}
factorial(100000); // 栈溢出
```

**解决方案**：

```rust
// 使用迭代
fn factorial(n: u64) -> u64 {
    (1..=n).product()
}
```

### 陷阱 4：忘记释放导出的内存

**问题**：

```rust
#[no_mangle]
pub extern "C" fn get_data() -> *mut u8 {
    let data = vec![1, 2, 3];
    let ptr = data.as_ptr() as *mut u8;
    std::mem::forget(data); // 泄漏！
    ptr
}
```

**解决方案**：

```rust
#[no_mangle]
pub extern "C" fn get_data() -> *mut u8 {
    Box::into_raw(Box::new([1u8, 2, 3])) as *mut u8
}

#[no_mangle]
pub extern "C" fn free_data(ptr: *mut u8) {
    unsafe { drop(Box::from_raw(ptr)); }
}
```

### 陷阱 5：浏览器差异

**问题**：

```javascript
// Chrome 支持，Safari 可能不支持
const memory = new WebAssembly.Memory({
    initial: 1,
    shared: true // Safari < 15.2 不支持
});
```

**解决方案**：

```javascript
// Feature detection
function supportsSharedMemory() {
    try {
        new WebAssembly.Memory({ initial: 1, shared: true });
        return true;
    } catch {
        return false;
    }
}

if (supportsSharedMemory()) {
    // 使用共享内存
} else {
    // 降级方案
}
```

---

## 调试最佳实践

### ✅ DO（推荐做法）

#### 1. 使用 Source Maps

```rust
// 编译时启用调试信息
cargo build --target wasm32-wasi -Cdebuginfo=2
```

#### 2. 添加日志钩子

```rust
#[cfg(target_arch = "wasm32")]
extern "C" {
    fn js_log(ptr: *const u8, len: usize);
}

#[macro_export]
macro_rules! log {
    ($($arg:tt)*) => {{
        let s = format!($($arg)*);
        unsafe {
            js_log(s.as_ptr(), s.len());
        }
    }};
}
```

#### 3. 使用断言

```rust
debug_assert!(index < buffer.len(), "Index out of bounds");
```

### ❌ DON'T（避免做法）

#### 1. 避免在生产环境留下调试代码

```rust
// BAD: 生产环境也会执行
println!("Debug: {:?}", data);

// GOOD: 仅开发环境
#[cfg(debug_assertions)]
println!("Debug: {:?}", data);
```

---

## 部署最佳实践

### ✅ DO（推荐做法）

#### 1. 启用压缩

```nginx
# nginx 配置
location ~ \.wasm$ {
    gzip on;
    gzip_types application/wasm;
    add_header Cache-Control "public, max-age=31536000";
}
```

**效果**：体积减少 40-60%

#### 2. 使用 CDN

```html
<script type="module">
    import init from 'https://cdn.example.com/v1.0.0/app.wasm';
    await init();
</script>
```

#### 3. 版本化部署

```text
/wasm/
  v1.0.0/
    app.wasm
  v1.0.1/
    app.wasm
  latest -> v1.0.1/
```

#### 4. 监控性能

```javascript
// 监控加载时间
const start = performance.now();
const { instance } = await WebAssembly.instantiateStreaming(
    fetch('app.wasm')
);
const loadTime = performance.now() - start;
analytics.track('wasm_load_time', loadTime);
```

---

## 性能检查清单

- [ ] 使用 AOT 编译（生产环境）
- [ ] 启用 SIMD 优化（适用场景）
- [ ] 使用 wasm-opt 优化
- [ ] 批量跨边界调用
- [ ] 使用共享内存（多线程）
- [ ] 预分配内存
- [ ] 避免频繁小分配
- [ ] 使用对象池（热路径）
- [ ] 启用 LTO
- [ ] 测量并优化热点

## 安全检查清单

- [ ] 验证所有输入边界
- [ ] 使用常量时间算法（密码学）
- [ ] 最小化 WASI 权限
- [ ] 启用溢出检查
- [ ] 不在 Wasm 中存储密钥
- [ ] 使用安全的随机数生成
- [ ] 及时更新依赖
- [ ] 启用内容安全策略（CSP）
- [ ] 审计第三方库
- [ ] 进行安全测试

## 调试检查清单

- [ ] 启用 Source Maps
- [ ] 添加日志钩子
- [ ] 使用断言
- [ ] 测试边界条件
- [ ] 使用 Sanitizers（开发环境）
- [ ] Profile 性能热点
- [ ] 测试内存泄漏
- [ ] 跨浏览器测试
- [ ] 回归测试
- [ ] 集成测试

## 部署检查清单

- [ ] 启用 gzip/brotli 压缩
- [ ] 使用 CDN
- [ ] 版本化部署
- [ ] 设置缓存策略
- [ ] 监控加载时间
- [ ] 监控错误率
- [ ] 准备回滚方案
- [ ] 灰度发布
- [ ] 压力测试
- [ ] 文档更新

---

## 参考资源

- [Rust Wasm Book](https://rustwasm.github.io/docs/book/)
- [Wasm Performance Guide](https://web.dev/webassembly-performance/)
- [Security Best Practices](https://webassembly-security.com/)

---

**版本历史**：

| 版本 | 日期 | 变更 |
|------|------|------|
| 1.0.0 | 2025-10-30 | 初始版本 |

---

_本文档将持续更新，欢迎贡献实践经验！_
