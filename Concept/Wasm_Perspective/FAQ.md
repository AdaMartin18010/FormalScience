# WebAssembly 常见问题（FAQ）

## 目录
- [基础概念](#基础概念)
- [技术原理](#技术原理)
- [性能与优化](#性能与优化)
- [安全与隔离](#安全与隔离)
- [应用场景](#应用场景)
- [工程实践](#工程实践)
- [批判性问题](#批判性问题)

---

## 基础概念

### Q1：WebAssembly 到底是什么？

**简答**：一种可移植的二进制指令格式，具有形式化验证语义和沙箱安全模型。

**形式化**：
\[
\text{Wasm} = (\text{BytecodeFormat}, \text{StackVM}, \text{TypeSystem}, \text{Sandbox})
\]

**三句话理解**：
1. **编码**：紧凑二进制格式（比 JS 小 30-50%）
2. **执行**：栈式虚拟机（可线性时间验证）
3. **安全**：内存沙箱（无法访问宿主内存）

---

### Q2：Wasm 与 JavaScript 的关系？

**协作关系**：
```
JavaScript（粘合层）
     ↕ （调用）
WebAssembly（计算核心）
```

**量化对比**：

| 维度 | JavaScript | WebAssembly |
|------|-----------|-------------|
| 解析 | 文本→AST（慢） | 二进制→验证（快 20×） |
| 启动 | JIT 预热 | 即时可用 |
| 峰值性能 | 动态优化 | 静态优化（稳定） |
| 类型 | 动态 | 静态（验证期） |
| 用途 | UI、逻辑 | 计算、算法 |

**互补性**：
\[
\text{Web App} = \text{JS}(\text{DOM, 事件}) + \text{Wasm}(\text{算法, 数据})
\]

---

### Q3：Wasm 能替代 JavaScript 吗？

**答案**：不能也不必要。

**技术原因**：
1. **DOM 访问**：需通过 JS 桥接（Interface Types 提案改善中）
2. **动态性**：Wasm 无动态代码生成（无 `eval`）
3. **生态系统**：npm 生态、框架、工具链

**哲学原因**：
> 抽象层次不同：JS 是高层协调语言，Wasm 是低层执行引擎。类比：导演 vs 演员。

**批判**：
> "替代论"是技术乐观主义幻觉。路径依赖决定：JS 霸权将延续，Wasm 是补充而非革命。

---

## 技术原理

### Q4：为什么是栈式虚拟机而非寄存器机？

**技术理由**：
1. **验证简单**：栈深度静态可知，\( O(n) \) 验证
2. **编码紧凑**：零地址指令，无寄存器分配
3. **可移植性**：无架构相关寄存器

**性能代价**：
\[
\text{Overhead}_{\text{stack→reg}} \approx 5-10\% \quad \text{（JIT 后）}
\]

**批判**：
> 这是"易验证 vs 易优化"的权衡。JVM 也选择了栈式，证明这是可接受的工程折衷。

---

### Q5：线性时间验证如何实现？

**算法核心**：
```
for each instruction:
    infer_stack_effect(instr)
    check_type_consistency()
    update_abstract_stack()
```

**复杂度**：
\[
T(n) = O(n) \quad \text{（单遍扫描）}
\]

**关键创新**：
1. **栈多态性**：`br` 指令类型 \( [t_1^*, t^*] \to [t_2^*] \)
2. **结构化控制流**：无任意 `goto`，验证期构建控制流图
3. **类型擦除**：运行时无类型标注

**定理**：
\[
\text{Validate}(M) \implies \neg \text{UndefinedBehavior}(M)
\]

---

### Q6：浮点确定性如何保证？

**规范要求**：
\[
\forall x, y : \texttt{f32.add}(x, y) = \text{IEEE-754-RoundTiesToEven}(x + y)
\]

**禁止优化**：
- 无 `ffast-math`
- 无 FMA 融合（除非 Relaxed SIMD 显式）
- 舍入模式固定

**性能代价**：
\[
\text{Slowdown} \approx 10-30\% \quad \text{（vs 原生 SIMD）}
\]

**应用**：区块链共识、科学计算

**批判**：
> 确定性是"语义确定"，非"物理确定"。硬件差异（如 ARM vs x86 浮点实现细节）仍可能导致极端情况下差异。

---

## 性能与优化

### Q7：Wasm 性能到底如何？

**基准测试**（SPEC CPU 2017，几何平均）：

| 编译策略 | 性能（vs 原生） |
|---------|----------------|
| 解释器 | 1-10% |
| 基线 JIT | 50-70% |
| 优化 JIT | 85-95% |
| AOT | 90-98% |

**影响因素**：
1. **编译策略**：解释 vs JIT vs AOT
2. **负载类型**：整数密集 > 浮点密集 > 内存密集
3. **SIMD 利用**：手动向量化可提升 2-4×

**实证案例**：
- Unity 游戏：85-90% 原生性能
- OpenCV 图像处理：70-80% 原生
- FFmpeg 转码：80-85% 原生

---

### Q8：如何优化 Wasm 性能？

**编译器层**：
```rust
// 启用 SIMD
#[target_feature(enable = "simd128")]
fn process_pixels(data: &[u8]) { ... }

// LTO + PGO
cargo build --release --features lto,pgo
```

**算法层**：
1. **减少边界检查**：提前一次性验证
2. **内存对齐**：64 字节对齐（缓存行）
3. **避免间接调用**：`call` 优于 `call_indirect`

**数据**：
\[
\text{Improvement} = 1.2-1.5× \quad \text{（综合优化）}
\]

---

### Q9：冷启动为何如此快？

**对比**（1 MB 模块）：

| 方案 | 启动时间 |
|------|---------|
| Docker 容器 | 500-800 ms |
| JVM | 200-300 ms |
| **Wasm (AOT)** | **2-5 ms** |

**原因**：
1. **流式验证**：边下载边验证
2. **无 GC 初始化**：线性内存即用
3. **代码共享**：只读代码段多实例共享

**形式化**：
\[
T_{\text{startup}} = T_{\text{validate}} + T_{\text{instantiate}} = O(n) + O(1)
\]

---

## 安全与隔离

### Q10：Wasm 沙箱真的安全吗？

**已防御**：
- ✅ 栈溢出 / ROP / JOP
- ✅ 堆溢出（边界检查）
- ✅ UAF（无指针类型）
- ✅ 类型混淆（运行时检查）

**未完全防御**：
- ⚠️ Spectre（需宿主缓解）
- ⚠️ 侧信道（时序泄漏）
- ⚠️ DoS（资源耗尽）
- ⚠️ 实现漏洞（JIT 编译器）

**形式化边界**：
\[
\text{Sandbox}_{\text{theory}} \not\Rightarrow \text{Sandbox}_{\text{practice}}
\]

**批判**：
> 沙箱保证"语法安全"，非"语义安全"。Spectre、Rowhammer 等硬件漏洞超出软件形式化能力。

---

### Q11：如何防御侧信道攻击？

**技术手段**：
1. **禁用高精度定时器**
2. **站点隔离**（浏览器）
3. **常量时间算法**（密码学）

**代码示例**：
```rust
// 常量时间比较（防时序泄漏）
fn ct_eq(a: &[u8], b: &[u8]) -> bool {
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}
```

**批判**：
> Wasm 无法强制常量时间，依赖程序员。这是抽象层次的本质局限。

---

### Q12：内存安全如何保证？

**形式化保证**：
\[
\forall a : \text{access}(a) \implies a < |\text{memory}| \vee \text{trap}
\]

**机制**：
1. **静态验证**：类型系统
2. **运行时检查**：每次 load/store 插桩
3. **硬件加速**：页保护（可选）

**开销**：
\[
\text{Overhead}_{\text{bounds-check}} \approx 5-10\%
\]

**优化**：
- 循环不变量外提
- 连续访问合并检查

---

## 应用场景

### Q13：Wasm 适合哪些场景？

**强适配场景**：

| 场景 | 理由 | 数据 |
|------|------|------|
| **Serverless** | 冷启动 <5 ms | 腾讯云：10k 实例/节点 |
| **边缘 AI** | GPU 加速 + 沙箱 | WasmEdge: 12 ms 推理（vs 11 ms 原生） |
| **IoT** | 差分 KB 级 + 热替换 | 工厂：年省 42 TB 流量 |
| **区块链** | 确定性 + 燃料计量 | Polkadot: TPS ↑18% |
| **插件系统** | 沙箱 + 跨语言 | OPA: 0.15 ms 策略评估 |

**不适配场景**：
- ❌ DOM 密集操作（桥接开销）
- ❌ 大堆（>4 GB，Memory64 改善中）
- ❌ 动态代码生成（无 JIT）

---

### Q14：为什么区块链选择 Wasm？

**技术原因**：
1. **确定性**：浮点 IEEE-754，无 UB
2. **可计量**：指令级燃料消耗
3. **沙箱**：恶意合约无法破坏节点
4. **跨链**：同一字节码多链运行

**案例**：
- Polkadot / Substrate
- EOSIO
- NEAR Protocol

**批判**：
> EVM 生态锁定强，Wasm 智能合约仍是"技术上优越，生态上劣势"的状态。网络效应 > 技术优越性。

---

### Q15：Wasm 能用于移动端吗？

**已落地**：
- Unity WebGL 导出（iOS/Android 浏览器）
- Flutter Web（部分 Wasm）
- React Native + Wasm 模块

**限制**：
- iOS 无 JIT（只能 AOT 或解释）
- 内存限制（Safari 1.5 GB）

**性能**：
\[
\text{Mobile} \approx 0.7-0.8 \times \text{Desktop} \quad \text{（同 Wasm 代码）}
\]

---

## 工程实践

### Q16：如何调试 Wasm？

**工具链**：
1. **Chrome DevTools**：支持断点、单步、变量查看
2. **Source Map**：映射回源码（DWARF）
3. **日志**：导入 `console.log` 宿主函数

**示例**：
```rust
#[no_mangle]
pub extern "C" fn debug_point(x: i32) {
    unsafe { log(x); }  // 导入宿主 log 函数
}
```

**批判**：
> 调试体验仍不及原生。栈回溯、变量检查需 DWARF 支持，工具链成熟度待提升。

---

### Q17：如何与现有代码集成？

**C/C++ 到 Wasm**：
```bash
emcc -O3 -s WASM=1 code.c -o code.wasm
```

**Rust 到 Wasm**：
```bash
cargo build --target wasm32-wasi --release
```

**JS 调用 Wasm**：
```javascript
const { instance } = await WebAssembly.instantiateStreaming(fetch('code.wasm'));
instance.exports.my_func(42);
```

**Wasm 调用 JS**（导入宿主函数）：
```wat
(import "env" "alert" (func $alert (param i32)))
```

---

### Q18：Wasm 的文件格式细节？

**魔数**：
```
00 61 73 6d  ; "\0asm"
01 00 00 00  ; version 1
```

**段顺序**：
\[
\text{Type} \prec \text{Import} \prec \text{Function} \prec \cdots \prec \text{Data}
\]

**编码**：LEB128 变长整数

**大小**：
\[
\text{Size}(\text{.wasm}) \approx 0.3-0.5 \times \text{Size}(\text{.js gzipped})
\]

---

## 批判性问题

### Q19：Wasm 是否是技术乐观主义的又一次失败？

**历史类比**：
- Java Applet → 失败（安全漏洞 + 启动慢）
- Flash → 失败（封闭生态 + 安全问题）
- NaCl → 半失败（Chrome 专属）

**Wasm 差异化**：
1. **开放标准**：W3C + 多厂商
2. **形式化验证**：线性时间验证
3. **生态中立**：无单一公司控制

**批判**：
> 技术优越性非成功充分条件。路径依赖、网络效应、标准化政治决定命运。Wasm 成功≠必然。

---

### Q20：形式化验证真的有用吗？

**有用之处**：
- 防止 UB（C/C++ 顽疾）
- 使静态分析可行
- 提供安全保障

**局限之处**：
- 无法防御硬件漏洞（Spectre）
- 无法防御实现错误（JIT 漏洞）
- 无法防御侧信道

**哲学反思**：
\[
\text{Formal} \not\Rightarrow \text{Secure} \quad \text{（哥德尔障碍）}
\]

> 形式化是必要的安全基础，非充分的安全保证。从数学到物理的映射，存在不可消除的语义鸿沟。

---

### Q21：Wasm 会取代 Docker 吗？

**相似性**：
- 都是沙箱隔离
- 都是跨平台
- 都是打包部署

**差异性**：

| 维度 | Docker | Wasm |
|------|--------|------|
| 粒度 | 进程级（MB 级） | 函数级（KB 级） |
| 启动 | 500 ms | 2 ms |
| 系统调用 | 全部（受限） | WASI 白名单 |
| 生态 | 成熟 | 新兴 |

**结论**：
> 共存而非替代。Docker 适合长驻服务，Wasm 适合短生命周期函数。

**批判**：
> "替代论"是零和思维。技术演化更多是分层共存（如 VM→Container→Wasm）。

---

### Q22：抽象税值得吗？

**成本**：
\[
\text{Overhead}_{\text{total}} = 5-15\% \quad \text{（性能）} + 1-2 \text{ ms/MB} \quad \text{（验证）}
\]

**收益**：
- 可移植性：一次编译，到处运行
- 安全性：沙箱 + CFI
- 确定性：跨平台一致

**权衡公式**：
\[
\text{Value} = \frac{\text{Portability} + \text{Security}}{\text{PerformanceTax}}
\]

**批判**：
> 是否值得取决于场景。高性能计算（HPC）不值得，边缘计算（Edge）值得。没有银弹，只有权衡。

---

## 参考资料

### 官方资源
- [WebAssembly Spec](https://webassembly.github.io/spec/)
- [MDN Wasm Guide](https://developer.mozilla.org/en-US/docs/WebAssembly)

### 学术论文
- [Haas17] "Bringing the Web up to Speed with WebAssembly." PLDI, 2017.
- [Watt18] "Mechanising and Verifying the WebAssembly Specification." CPP, 2018.

### 工具链
- [Emscripten](https://emscripten.org/)
- [wasm-pack](https://rustwasm.github.io/wasm-pack/)
- [WasmEdge](https://wasmedge.org/)

---

**总结**：
> WebAssembly 不是银弹，而是工具箱中的又一工具。理解其边界、权衡与限制，方能理性应用。本 FAQ 旨在超越技术乐观主义与悲观主义，提供基于形式化、实证与批判的全面视角。
