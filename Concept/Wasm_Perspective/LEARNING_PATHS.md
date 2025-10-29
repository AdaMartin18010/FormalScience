# WebAssembly 学习路径 (Learning Paths)

## 概述

本文档提供四条定制化学习路径，对应不同角色与目标。每条路径包含：
- 📚 必读文档
- ⏱️ 预估时间
- 🎯 学习目标
- ✅ 自检清单

---

## 路径一：开发者实践路径

### 目标
掌握 Wasm 开发基础，能独立构建和部署 Wasm 应用。

### 时间
**8-12 小时**

### 路线图

```
Day 1 (3h)
  ├─ README (1h)
  ├─ QUICK_REFERENCE (0.5h)
  ├─ 01.1 形式化语义（概览）(1h)
  └─ 实践：编译第一个 Wasm 模块 (0.5h)

Day 2 (4h)
  ├─ 02.1 模块结构 (1h)
  ├─ 02.2 指令集架构 (1.5h)
  └─ 实践：手写 WAT，理解指令 (1.5h)

Day 3 (5h)
  ├─ 03.1 编译策略 (1h)
  ├─ 04.1 WASI 接口 (1.5h)
  ├─ 实践：集成 Rust 项目 (2h)
  └─ FAQ Q1-Q10 (0.5h)
```

### 必读文档
1. **README**：整体认知
2. **01.1 形式化语义**：理解执行模型
3. **02.1 模块结构**：掌握二进制格式
4. **02.2 指令集架构**：熟悉指令集
5. **03.1 编译策略**：选择合适编译器
6. **04.1 WASI 接口**：系统集成
7. **QUICK_REFERENCE**：速查手册
8. **FAQ**（Q1-Q10）：常见问题

### 实践项目
```rust
// Rust -> Wasm
#[no_mangle]
pub extern "C" fn fibonacci(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n-1) + fibonacci(n-2)
    }
}
```

编译并优化：
```bash
cargo build --target wasm32-wasi --release
wasm-opt -O3 target/wasm32-wasi/release/fib.wasm -o fib_opt.wasm
```

### 自检清单
- [ ] 能解释 Wasm 的三大特性（可移植、安全、确定性）
- [ ] 能手写简单的 WAT 代码
- [ ] 理解类型系统和栈式执行
- [ ] 能编译 C/Rust 到 Wasm
- [ ] 能在 Node.js 和浏览器中运行 Wasm
- [ ] 理解 WASI 的作用

---

## 路径二：研究者理论路径

### 目标
深入理解 Wasm 的形式化基础，能进行理论分析与扩展。

### 时间
**1-2 周**

### 路线图

```
Week 1: 理论基础
  ├─ 00_Master_Index (2h)
  ├─ 01.1 形式化语义 (4h)
  ├─ 01.2 类型系统 (4h)
  ├─ 01.3 验证模型 (4h)
  ├─ 01.4 执行模型 (3h)
  ├─ 01.5 安全模型 (3h)
  └─ 阅读论文：[Watt18, Haas17] (4h)

Week 2: 哲学与批判
  ├─ 06.1 可移植性理论 (3h)
  ├─ 06.2 安全哲学 (3h)
  ├─ 06.3 确定性认识论 (3h)
  ├─ 06.4 抽象层次论 (2h)
  ├─ 08.3 理论极限 (2h)
  ├─ 08.4 研究前沿 (2h)
  └─ 撰写批判性分析 (5h)
```

### 必读文档
**核心理论**：
1. 01 理论基础（全系列）
2. 06 哲学基础（全系列）
3. 08.3 理论极限
4. 08.4 研究前沿

**工具方法**：
5. GLOSSARY（符号表）
6. FAQ（批判性问题 Q19-Q22）

### 必读论文
1. **[Haas17]** "Bringing the Web up to Speed with WebAssembly." PLDI, 2017.
2. **[Watt18]** "Mechanising and Verifying the WebAssembly Specification." CPP, 2018.
3. **[Rossberg]** "WebAssembly Type System Specification." W3C, 2023.
4. **[Pierce02]** *Types and Programming Languages.* (相关章节)

### 研究方向
1. **形式化验证**
   - 端到端验证（源码→Wasm→原生）
   - 并发语义机械化

2. **类型系统扩展**
   - 依赖类型（精化类型）
   - 线性类型（资源管理）

3. **性能理论**
   - 抽象税的下界证明
   - 最优编译策略选择

4. **安全模型**
   - 信息流控制
   - 侧信道防御形式化

### 自检清单
- [ ] 能形式化定义 Wasm 操作语义
- [ ] 能证明 Progress 和 Preservation 定理
- [ ] 理解验证算法的线性时间复杂度
- [ ] 能批判性分析技术限制
- [ ] 熟悉主流形式化工具（Isabelle、Coq）
- [ ] 能提出研究问题

---

## 路径三：架构师决策路径

### 目标
评估 Wasm 在特定场景的适用性，进行技术选型与成本收益分析。

### 时间
**1 天（8 小时）**

### 路线图

```
Morning (4h)
  ├─ 00_Master_Index (0.5h)
  ├─ README (0.5h)
  ├─ 03.5 性能分析 (1h)
  ├─ 07.1 性能经济学 (1h)
  └─ 07.3 成本收益分析 (1h)

Afternoon (4h)
  ├─ 05.1 Serverless 边缘 (1h)
  ├─ 05.2 IoT 嵌入式 (1h)
  ├─ 05.3 微服务网格 (0.5h)
  ├─ FAQ Q13-Q18 (1h)
  └─ 案例研究与决策矩阵 (0.5h)
```

### 必读文档
**性能评估**：
1. 03.5 性能分析
2. 07.1 性能经济学
3. QUICK_REFERENCE（性能数据）

**应用模式**：
4. 05.1 Serverless 边缘
5. 05.2 IoT 嵌入式
6. 05.3 微服务网格
7. 05.4 插件系统
8. 05.5 区块链合约

**决策支持**：
9. 07.3 成本收益分析
10. FAQ（应用场景 Q13-Q15）

### 决策矩阵

| 场景特征 | 权重 | Wasm 得分 | 容器得分 | 虚拟机得分 |
|---------|------|-----------|---------|-----------|
| 冷启动 | 高 | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐ |
| 内存密度 | 高 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐ |
| 峰值性能 | 中 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| 生态成熟度 | 高 | ⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| 安全隔离 | 高 | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |

### ROI 计算模板

```python
# 年节省成本估算
def calculate_savings(num_nodes):
    # 流量节省（差分更新）
    traffic_savings = num_nodes * 200  # MB 镜像 → 50 KB 差分
    traffic_cost = traffic_savings * 0.05  # USD/GB

    # 内存节省（高密度）
    memory_savings = num_nodes * 36  # 40 MB → 4 MB
    memory_cost = memory_savings * 0.01  # USD/GB/month

    # 研发节省（跨平台）
    devops_savings = 0.2 * 80000  # 20% 人日

    return traffic_cost + memory_cost + devops_savings

# 10k 边缘节点
print(f"Annual Savings: ${calculate_savings(10000):,.0f}")
# Output: $115,000
```

### 自检清单
- [ ] 理解 Wasm vs 容器 vs 虚拟机的权衡
- [ ] 能评估特定场景的适用性
- [ ] 能计算 ROI 和盈亏平衡点
- [ ] 理解生态系统限制
- [ ] 能制定迁移路径

---

## 路径四：全栈综合路径

### 目标
全面掌握 Wasm 的理论、技术与实践，能独立研发和优化复杂系统。

### 时间
**3-4 周**

### 路线图

```
Week 1: 理论基础
  ├─ 00_Master_Index
  ├─ 01 理论基础（全系列）
  ├─ 02 二进制格式（核心章节）
  └─ 实践：实现简单验证器

Week 2: 运行时与集成
  ├─ 03 运行时系统（全系列）
  ├─ 04 系统集成（全系列）
  └─ 实践：构建 WasmEdge 插件

Week 3: 应用与经济学
  ├─ 05 应用模式（全系列）
  ├─ 07 工程经济学（全系列）
  └─ 实践：Serverless 边缘部署

Week 4: 哲学批判与未来
  ├─ 06 哲学基础（全系列）
  ├─ 08 未来方向（全系列）
  ├─ FAQ（全部）
  └─ 项目：开源贡献或论文
```

### 必读文档
**全部 40+ 篇文档**，按主索引顺序。

### 综合项目

**项目：边缘 AI 推理平台**

需求：
- 冷启动 <5 ms
- 支持多模型热替换
- GPU 加速
- 沙箱隔离
- 成本优化

技术栈：
- WasmEdge（运行时）
- WASI-NN（推理接口）
- Rust（模型加载）
- Kubernetes + crun（编排）

关键指标：
- 性能：85-90% 原生
- 密度：10k 实例/节点
- ROI：<6 个月

### 自检清单
- [ ] 能独立设计 Wasm 运行时架构
- [ ] 能进行形式化验证
- [ ] 能优化性能至接近原生
- [ ] 能评估经济效益
- [ ] 能批判性分析技术限制
- [ ] 能为开源社区贡献

---

## 学习资源

### 官方资源
- [WebAssembly Spec](https://webassembly.github.io/spec/)
- [MDN Wasm Guide](https://developer.mozilla.org/en-US/docs/WebAssembly)
- [WASI](https://github.com/WebAssembly/WASI)

### 形式化工具
- [Isabelle/Wasm](https://github.com/isabelle-prover/isabelle-wasm)
- [Wasm-Coq](https://github.com/WasmCert/WasmCert-Coq)
- [K-Wasm](https://github.com/kframework/wasm-semantics)

### 运行时
- [WasmEdge](https://wasmedge.org/)
- [Wasmtime](https://wasmtime.dev/)
- [Wasmer](https://wasmer.io/)

### 社区
- [WebAssembly Community Group](https://www.w3.org/community/webassembly/)
- [Bytecode Alliance](https://bytecodealliance.org/)

---

## 进阶方向

### 方向一：性能优化专家
- 深入编译器优化
- SIMD 与 GPU 加速
- 性能分析工具开发

### 方向二：安全研究
- 侧信道防御
- 形式化验证
- 漏洞挖掘

### 方向三：标准化贡献
- 提案编写
- 规范审查
- 实现反馈

### 方向四：生态建设
- 语言前端开发
- 工具链完善
- 最佳实践总结

---

## 学习建议

### 理论与实践结合
```
理论学习 → 实践验证 → 批判反思 → 迭代深化
```

### 多角度验证
1. **形式化**：数学证明
2. **实证**：基准测试
3. **批判**：揭示限制

### 社区参与
- 参与 GitHub 讨论
- 贡献开源项目
- 撰写博客文章

---

**学习心态**：
> WebAssembly 不是银弹，而是工具箱中的又一工具。保持批判性思维，理解其边界与权衡，方能理性应用。

*本学习路径旨在提供系统化、个性化的知识获取路线，帮助不同背景的学习者高效达成目标。*
