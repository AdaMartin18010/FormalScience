# Scheduling System Documentation: Content Assessment & Filling Plan

**Project:** FormalScience
**Assessment Date:** 2026-04-14
**Scope:** Scheduling-related docs across `docs/Refactor/`, `Composed/`, `Concept/`, `FormalRE/`

---

## Executive Summary

The project contains **~220 scheduling-related markdown documents** across multiple directories. Quality is **bimodal**:

- **`docs/Refactor/06_调度系统/`** (33 files): **High quality** — mathematically rigorous, concise, with Rust/Haskell/Lean code, formal proofs, and strong cross-references.
- **`Composed/schedule_formal_view/`** (~180 files): **Highly variable** — some deep-dive documents are excellent (Kubernetes, Linux kernel, disk I/O, GPU, DB), but many suffer from **massive template boilerplate** ("思维表征体系" consuming 30–50% of file length) and shallow content in emerging domains (LLM, Serverless, quantum, confidential computing).
- **`Concept/16_GPU与加速器调度/` & `17_数据库调度系统/`** (8 files): **High quality** — formal, theorem-driven, complementary to Composed content.

**Bottom line:** The core theoretical and systems content is surprisingly strong. The biggest gaps are (1) **underdeveloped emerging domains**, (2) **compiler scheduling depth**, (3) **industrial real-time systems context**, (4) **cross-layer integration**, and (5) **completing formal Lean proofs** (many bodies use `sorry`).

---

## 1. Document Inventory by Category

### 1.1 Primary Directories

| Directory | File Count (MD) | Total Lines (approx) | Quality Tier |
|-----------|----------------|----------------------|--------------|
| `docs/Refactor/06_调度系统/` | 33 | ~14,000 | **High** |
| `Composed/schedule_formal_view/` | ~180 | ~180,000 | **Mixed (High–Low)** |
| `Concept/16_GPU与加速器调度/` | 4 | ~4,600 | **High** |
| `Concept/17_数据库调度系统/` | 4 | ~6,900 | **High** |
| `examples/lean/` | 12 (incl. `08_Scheduling.lean`) | ~1,100 | **Medium** |

### 1.2 Detailed Category Breakdown

#### A. CPU / Hardware Scheduling

| Source | Documents | Avg Size | Assessment |
|--------|-----------|----------|------------|
| `docs/Refactor/06_调度系统/02_硬件调度/` | 6 files | ~450 lines | **High** — Tomasulo algorithm, branch prediction (Gshare), SMT, with Rust/Haskell implementations and Lean specs. |
| `Composed/schedule_formal_view/01_CPU硬件层/` | 10+ files | ~800 lines | **High** for architecture docs; CPU scheduling-specific docs are shorter but solid. |

**Missing:** Side-by-side comparison of x86 vs. ARM vs. RISC-V scheduling hardware differences.

#### B. OS Abstraction Layer

| Source | Documents | Avg Size | Assessment |
|--------|-----------|----------|------------|
| `docs/Refactor/06_调度系统/03_OS调度/` | 5 files | ~520 lines | **High** — CFS vruntime math, MLFQ Rust impl, EDF schedulability, Linux integration. |
| `Composed/schedule_formal_view/03_OS抽象层/` | 8 + Linux deep dive | ~600 lines | **Medium–High** — Linux deep analysis (1,449 lines) is excellent but buried in template-heavy companion files. |

**Missing:** Windows Scheduler and macOS GCD comparisons to Linux CFS.

#### C. Storage Scheduling

| Source | Documents | Avg Size | Assessment |
|--------|-----------|----------|------------|
| `docs/Refactor/06_调度系统/02_硬件调度/02.3_存储调度.md` | 1 | ~485 lines | **Medium** — covers elevator algorithms. |
| `Composed/schedule_formal_view/14_存储调度系统/` | 6 files | ~1,100 lines | **High** — disk I/O doc is a standout with CFQ/Deadline/BFQ/NOOP Python implementations, Linux blk-mq architecture, cgroup blkio QoS scripts, and latency decomposition. |

**Missing:** NVMe multi-queue scheduling (Linux mq-deadline, kyber, bfq for NVMe) and SPDK user-space I/O scheduling.

#### D. Network Scheduling

| Source | Documents | Avg Size | Assessment |
|--------|-----------|----------|------------|
| `docs/Refactor/06_调度系统/02_硬件调度/02.4_网络调度.md` | 1 | ~467 lines | **Medium** — packet scheduling basics. |
| `Composed/schedule_formal_view/15_网络调度系统/` | 8 files | ~1,400 lines | **Medium–High** — Content on WFQ/DRR/FQ-CoDel/DPDK is solid, but ~40% of each file is repetitive template boilerplate. |

**Missing:** eBPF/XDP scheduling programs (actual C code), DCTCP/HPCC datacenter congestion control, and P4/programmable switch scheduling.

#### E. GPU & Accelerator Scheduling

| Source | Documents | Avg Size | Assessment |
|--------|-----------|----------|------------|
| `Concept/16_GPU与加速器调度/` | 4 files | ~1,150 lines | **High** — rigorous formal definitions, SM/Warp architecture, CUDA source analysis. |
| `Composed/schedule_formal_view/16_GPU与加速器调度/` | 8 files | ~900 lines | **High** — excellent practical coverage of CUDA Streams, Graphs, MPS, MIG, multi-GPU parallelism, Roofline model, real A100 bandwidth numbers. |

**Missing:** AMD ROCm/HIP scheduling comparison, Intel Xe GPU scheduling, and MLCommons scheduling benchmarks.

#### F. Database Scheduling

| Source | Documents | Avg Size | Assessment |
|--------|-----------|----------|------------|
| `Concept/17_数据库调度系统/` | 4 files | ~1,725 lines | **High** — strong formalization of query optimization as NP-complete, MySQL/PostgreSQL optimizer internals, cost model formulas, parallel query plans. |
| `Composed/schedule_formal_view/17_数据库调度系统/` | 8 files | ~1,100 lines | **High** — query optimization, concurrency control, distributed/cloud-native DB scheduling. |

**Missing:** Vector database scheduling (Milvus, Pinecone), learned query optimizers (Neo, Bao), and cloud DWH (Snowflake, BigQuery) resource scheduling.

#### G. Compiler Optimization Scheduling

| Source | Documents | Avg Size | Assessment |
|--------|-----------|----------|------------|
| `Composed/schedule_formal_view/18_编译器调度优化/` | 4 files | ~660 lines | **Medium** — 18.1_指令调度.md is the weakest major doc. ~50% template fluff. Actual content covers list scheduling, modulo scheduling, trace scheduling at a high school textbook level. No LLVM/GCC pass analysis, no real IR examples. |

**Missing:** LLVM MachineScheduler and PostRAScheduler analysis, MIR examples, register pressure heuristics in LLVM, and SPEC CPU benchmark results.

#### H. Real-Time Systems

| Source | Documents | Avg Size | Assessment |
|--------|-----------|----------|------------|
| `docs/Refactor/06_调度系统/03_OS调度/03.1_进程调度.md` | 1 (section) | — | **High** — RM/EDF math and Rust implementation. |
| `Composed/schedule_formal_view/19_实时系统调度/` | 4 files | ~670 lines | **Medium** — boilerplate-heavy. Covers RMS/EDF/WCET basics but lacks industrial context. |

**Missing:** Industrial RTOS (VxWorks, RT-Linux, QNX, AUTOSAR OS), WCET analysis tools (aiT, Bound-T), DO-178C certification, and TSN scheduling.

#### I. Formal Proofs

| Source | Documents | Avg Size | Assessment |
|--------|-----------|----------|------------|
| `docs/Refactor/06_调度系统/05_形式化证明/` | 7 docs + 1 report | ~350 lines/doc | **High** — SPT optimality, EDF optimality, NP-hardness reductions, online scheduling competitive ratio, Liu & Layland bound. |
| `docs/Refactor/06_调度系统/05_形式化证明/lean_proofs/` | 10 .lean files | ~50–350 lines/file | **Medium** — Files exist but many theorems in markdown docs end with `sorry`. The .lean files are real but may also be incomplete stubs. |
| `Composed/schedule_formal_view/09_形式化理论与证明/` | 7 docs | ~550 lines | **Medium** — hardware-OS mapping proofs, performance bounds, banker's algorithm, page replacement. Some good content, some boilerplate. |

**Missing:** Complete, compilable Lean 4 proofs for all 10 claimed theorems (many currently use `sorry`).

#### J. Distributed / Cloud / Emerging

| Source | Documents | Avg Size | Assessment |
|--------|-----------|----------|------------|
| `docs/Refactor/06_调度系统/04_分布式调度/` | 5 files | ~550 lines | **Medium** — YARN/K8s/Spark/Flink mentioned but not deeply analyzed. |
| `Composed/schedule_formal_view/Kubernetes调度深度分析.md` | 1 | ~5,118 lines | **High** — Exceptional depth (kube-scheduler v1.28+ source analysis, predicates/priorities, scheduling framework, Rust implementation). |
| `Composed/schedule_formal_view/25_LLM推理调度/` | 4 files | ~485 lines | **Low–Medium** — Small files. Basic Transformer/KV-Cache/batching concepts. No vLLM/SGLang/TensorRT-LLM scheduler internals. |
| `Composed/schedule_formal_view/26_Serverless调度/` | 4 files | ~420 lines | **Low–Medium** — Cold start, warmup, elasticity. No AWS Lambda/Knative scheduler deep dive. |
| `Composed/schedule_formal_view/27_机密计算调度/` | 1 file | ~545 lines | **Low** — Only one file (TEE基础). Incomplete section. |
| `Composed/schedule_formal_view/22_量子计算调度/` | 4 files | ~600 lines | **Low–Medium** — High-level quantum gate scheduling. No IBM Qiskit/Google Cirq concrete examples. |

---

## 2. Content Quality Summary by Category

| Category | Quality | Key Strength | Key Weakness |
|----------|---------|--------------|--------------|
| **Theory & Formal Proofs** | High | Graham notation, NP-hardness proofs, Lean 4 integration | Many `sorry` placeholders in proofs |
| **CPU/Hardware Scheduling** | High | Tomasulo, branch prediction, SMT with code | Missing ISA comparison (x86/ARM/RISC-V) |
| **OS Scheduling** | High | CFS math, MLFQ/EDF Rust impl, Linux deep dive | Missing Windows/macOS comparisons |
| **Storage Scheduling** | High | blk-mq, CFQ/Deadline/BFQ/NOOP Python code | Light on NVMe-specific schedulers |
| **GPU Scheduling** | High | CUDA Streams/Graphs/MPS/MIG, Roofline, real perf data | Missing AMD ROCm/Intel Xe |
| **DB Scheduling** | High | Query optimizer internals, cost models, NP-completeness | Missing vector DB/cloud DWH |
| **Network Scheduling** | Medium-High | WFQ/DRR/FQ-CoDel, DPDK, Linux net/sched | Heavy template boilerplate |
| **Compiler Scheduling** | Medium | Covers basic algorithms | No LLVM/GCC pass analysis; shallow |
| **Real-Time Systems** | Medium | RMS/EDF theory present | No industrial RTOS/DO-178C/WCET tools |
| **Distributed (K8s)** | High | K8s deep dive exists (222KB) | Not integrated into docs/Refactor structure |
| **LLM/Serverless/Emerging** | Low-Medium | Trendy topics covered | Files are small (~15KB), high-level only |

---

## 3. Top 10 Priority Documents to Fill / Improve

### Priority 1: Complete Lean 4 Formal Proofs

**Target:** `docs/Refactor/06_调度系统/05_形式化证明/lean_proofs/*.lean`
**Current State:** 10 .lean files exist, but markdown docs explicitly mark many theorem bodies with `sorry`.
**Requirements:**

- Replace all `sorry` with complete, compilable Lean 4 proofs.
- Add `lakefile.toml` + GitHub Actions CI to verify proofs on push.
- Link each .lean file back to the corresponding markdown theorem statement.
**Estimated Effort:** 3–4 weeks (expert in Lean 4 + scheduling theory)

---

### Priority 2: Compiler Scheduling — LLVM Deep Dive

**Target:** `Composed/schedule_formal_view/18_编译器调度优化/18.1_指令调度.md` (major rewrite) + new `18.5_LLVM调度Pass分析.md`
**Current State:** High-level textbook content; ~50% template fluff. No industrial compiler internals.
**Requirements:**

- Add LLVM MachineScheduler pipeline analysis (pre-RA, post-RA).
- Include actual LLVM MIR snippets showing before/after scheduling.
- Explain ScheduleDAG, DFA (resource constraint modeling), and Heuristic (e.g., BottomUpIGList).
- Add SPEC CPU2017 benchmark results showing impact of scheduling on IPC.
- Remove or condense repetitive template sections.
**Estimated Effort:** 1.5 weeks

---

### Priority 3: Industrial Real-Time Systems & Certification

**Target:** New `19.5_工业实时系统与认证.md` + update `19.1_硬实时调度.md`, `19.4_实时调度验证.md`
**Current State:** Academic RM/EDF only. No connection to aerospace/automotive practice.
**Requirements:**

- Compare VxWorks, RT-Linux (PREEMPT_RT), QNX, AUTOSAR OS schedulers.
- Introduce DO-178C (aviation) and ISO 26262 (automotive) scheduling requirements.
- Document WCET analysis tools: aiT, Bound-T, Sweet.
- Add TSN (IEEE 802.1Qbv/Qbu) time-aware shaper scheduling for networked RT.
- Code example: configure SCHED_DEADLINE in Linux PREEMPT_RT.
**Estimated Effort:** 1.5 weeks

---

### Priority 4: LLM Inference Scheduling (vLLM / SGLang / TensorRT-LLM)

**Target:** `Composed/schedule_formal_view/25_LLM推理调度/` (expand all 4 files)
**Current State:** ~485 lines total. Only basic Transformer/KV-Cache explained.
**Requirements:**

- **vLLM scheduler:** continuous batching, PagedAttention memory manager, preemption/swap logic.
- **SGLang:** radix attention scheduling, structured generation scheduling.
- **TensorRT-LLM:** in-flight batching, KV-cache manager.
- Mathematical model: optimize throughput under TTFT/TBT SLO constraints.
- Python pseudocode for a simple continuous-batching scheduler.
- Performance numbers: compare static vs. continuous batching on Llama-3-70B.
**Estimated Effort:** 1.5 weeks

---

### Priority 5: Serverless / Function-as-a-Service Scheduling

**Target:** `Composed/schedule_formal_view/26_Serverless调度/` (expand all 4 files)
**Current State:** ~420 lines total. Generic cold-start discussion.
**Requirements:**

- Deep dive into AWS Lambda placement algorithm (firecracker microVM scheduling).
- Knative/Kubernetes-based FaaS scheduling (KEDA autoscaler, scale-from-zero).
- Formal model: cold-start latency vs. keep-alive cost optimization.
- Rust/Python implementation of a simple function scheduler with predictive pre-warming.
- Comparison: AWS Lambda vs. Azure Functions vs. Cloudflare Workers scheduling.
**Estimated Effort:** 1 week

---

### Priority 6: Cross-Layer End-to-End Scheduling Latency Analysis

**Target:** New `docs/Refactor/06_调度系统/06_端到端调度延迟分析.md`
**Current State:** No document traces a single request through all layers.
**Requirements:**

- Define a unified latency model: L_total = L_CPU + L_OS + L_container + L_K8s + L_network + L_storage.
- Walk through a concrete example: "Deploy a microservice Pod in Kubernetes, handle an HTTP request, query PostgreSQL."
- At each layer, identify the scheduling decision, queueing delay, and context-switch overhead.
- Include latency budgets (ns -> us -> ms) and where scheduling overhead dominates.
- Mermaid diagram showing the full stack scheduling path.
**Estimated Effort:** 1 week

---

### Priority 7: Kubernetes Scheduler Integration into Refactor Docs

**Target:** Expand `docs/Refactor/06_调度系统/04_分布式调度/04.1_集群调度.md`
**Current State:** Excellent 222KB K8s doc exists in Composed but is isolated from the high-quality Refactor docs.
**Requirements:**

- Synthesize the kube-scheduler deep dive into the Refactor doc format (concise, formal, code-heavy).
- Add Kubernetes Scheduling Framework (v1.28+) plugin architecture.
- Include Go code snippets for custom Filter and Score plugins.
- Formalize Pod-to-Node assignment as a constraint satisfaction problem.
- Add DRF (Dominant Resource Fairness) connection to K8s resource quotas.
**Estimated Effort:** 1 week

---

### Priority 8: Network Scheduling — Remove Boilerplate & Add eBPF/XDP Code

**Target:** Rewrite `Composed/schedule_formal_view/15_网络调度系统/15.1_网络包调度.md` and `15.3_网络拥塞控制.md`
**Current State:** Solid technical content buried under ~40% generic template sections.
**Requirements:**

- Strip generic "思维表征体系" boilerplate down to one concise mind map.
- Add actual eBPF/XDP packet scheduling C code (token bucket or FQ-CoDel skeleton).
- Add DCTCP and HPCC datacenter congestion control algorithms with pseudo-code.
- Compare Linux tc implementations: htb, fq_codel, cake.
- Performance data: single-core packet throughput for FIFO vs. DRR vs. FQ-CoDel.
**Estimated Effort:** 1 week

---

### Priority 9: Vector Database & Cloud DWH Scheduling

**Target:** New `Composed/schedule_formal_view/17_数据库调度系统/17.5_向量数据库调度.md` + `17.6_云数据仓库调度.md`
**Current State:** Excellent relational DB content, but no coverage of modern vector/cloud analytics scheduling.
**Requirements:**

- **Vector DB:** Milvus/Pinecone segment loading, GPU index scheduling, HNSW/IVF search parallelism.
- **Cloud DWH:** Snowflake virtual warehouse scheduling, BigQuery slot scheduler, Databricks SQL warehouse auto-scaling.
- Cost models: query latency vs. dollar cost trade-offs.
- Python simulation of a vector DB segment scheduler.
**Estimated Effort:** 1 week

---

### Priority 10: NVMe & SPDK Storage Scheduling

**Target:** New `Composed/schedule_formal_view/14_存储调度系统/14.5_NVMe与SPDK调度.md`
**Current State:** Excellent HDD/SSD content, but NVMe multi-queue and user-space SPDK scheduling are missing.
**Requirements:**

- Explain Linux blk-mq hardware/software queue mapping.
- Compare mq-deadline, kyber, bfq for NVMe.
- SPDK scheduler architecture: reactor threads, poll-mode I/O, bdev layer scheduling.
- C code example: simple SPDK I/O scheduler prioritizing reads over writes.
- Benchmark data: IOPS/latency for different NVMe schedulers on Gen5 SSDs.
**Estimated Effort:** 1 week

---

## 4. Summary Table: Priority Documents to Fill/Improve

| Priority | Document(s) | Category | What to Add | Effort |
|----------|-------------|----------|-------------|--------|
| 1 | `lean_proofs/*.lean` | Formal Proofs | Complete `sorry`-free Lean 4 proofs + CI | 3–4 wks |
| 2 | `18.1_指令调度.md` + `18.5_LLVM调度Pass分析.md` | Compiler | LLVM MIR, MachineScheduler, SPEC benchmarks | 1.5 wks |
| 3 | `19.5_工业实时系统与认证.md` | Real-Time | VxWorks, PREEMPT_RT, DO-178C, aiT, TSN | 1.5 wks |
| 4 | `25.x_LLM推理调度/` | Emerging AI | vLLM, SGLang, TensorRT-LLM schedulers | 1.5 wks |
| 5 | `26.x_Serverless调度/` | Emerging FaaS | AWS Lambda, Knative, pre-warming model | 1 wk |
| 6 | `06_端到端调度延迟分析.md` (new) | Integration | Unified cross-layer latency model + walkthrough | 1 wk |
| 7 | `04.1_集群调度.md` (expand) | Distributed | K8s Scheduling Framework, custom plugins | 1 wk |
| 8 | `15.1_网络包调度.md` + `15.3_网络拥塞控制.md` | Network | eBPF/XDP code, DCTCP/HPCC, strip boilerplate | 1 wk |
| 9 | `17.5_向量数据库调度.md` + `17.6_云数据仓库调度.md` (new) | Database | Milvus, Snowflake, BigQuery scheduling | 1 wk |
| 10 | `14.5_NVMe与SPDK调度.md` (new) | Storage | blk-mq, kyber, SPDK reactor scheduling | 1 wk |

**Total Estimated Effort:** ~12–14 weeks of focused writing (1 FTE)

---

## 5. Recommendations for Execution

1. **Start with Lean proofs (Priority 1)** — this is the project's unique differentiator. A fully verified Lean 4 proof library generates far more credibility than 20 additional survey documents.
2. **Parallelize emerging domains (Priorities 4 & 5)** — LLM and Serverless scheduling are the highest-value "trending" topics that external readers will search for.
3. **Create a boilerplate cleanup script** for `Composed/schedule_formal_view/` — many files have identical "思维表征体系" headers that can be programmatically condensed to save ~30% file size and improve readability.
4. **Migrate K8s/Linux deep dives** from `Composed/` root into `docs/Refactor/06_调度系统/` structure to ensure the highest-quality docs are in the canonical location.
5. **Do NOT create new empty template files** for quantum/neuromorphic/optical scheduling unless there is a concrete plan to fill them with mathematical models and code. The existing small files in these domains already risk looking like placeholders.

---

## Appendix: Methodology Notes

- **Sampling method:** Read representative files from each major category in full; spot-checked directory listings and file sizes for coverage estimation.
- **Quality criteria assessed:** Presence of (a) formal mathematical definitions, (b) algorithm analysis (complexity/correctness), (c) code examples, (d) comparisons to real systems (Linux/Kubernetes/etc.), (e) actual performance data or benchmarks.
- **Files inspected in detail:**
  - `docs/Refactor/06_调度系统/02.1_CPU调度.md`
  - `docs/Refactor/06_调度系统/03.1_进程调度.md`
  - `docs/Refactor/06_调度系统/05.1_调度系统核心定理证明.md`
  - `docs/Refactor/06_调度系统/05.6_定理证明Lean实现.md`
  - `docs/Refactor/06_调度系统/05_形式化证明/lean_proofs/*.lean`
  - `Composed/schedule_formal_view/14.1_磁盘IO调度.md`
  - `Composed/schedule_formal_view/15.1_网络包调度.md`
  - `Composed/schedule_formal_view/16.1_GPU计算调度.md`
  - `Composed/schedule_formal_view/17.1_查询调度.md`
  - `Composed/schedule_formal_view/18.1_指令调度.md`
  - `Composed/schedule_formal_view/19.1_硬实时调度.md`
  - `Composed/schedule_formal_view/Kubernetes调度深度分析.md`
  - `Composed/schedule_formal_view/Linux内核调度深度分析.md`
  - `Concept/16_GPU与加速器调度/16.1_GPU计算调度.md`
