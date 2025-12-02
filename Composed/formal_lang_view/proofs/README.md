# 形式化验证代码库

> **目录**: formal_lang_view/proofs/
> **创建日期**: 2025-12-02
> **文档状态**: ✅ 完成

---

## 📋 目录结构

```text
proofs/
├── README.md          # 本文件
├── coq/               # Coq证明
│   ├── BasicTypes.v   # 基本类型定义
│   ├── ImageLayers.v  # 镜像层理论
│   └── Functors.v     # 函子证明
├── lean4/             # Lean4证明
│   ├── BasicTypes.lean
│   └── ResourceSafety.lean
└── tla+/              # TLA+规约
    └── Scheduling.tla
```

---

## 1 Coq证明

### 1.1 基本类型定义 (`BasicTypes.v`)

定义基础设施中的核心类型及其属性。

### 1.2 镜像层理论 (`ImageLayers.v`)

证明OCI镜像层与类型系统的对应关系。

### 1.3 函子证明 (`Functors.v`)

证明类型-调度映射函子的满忠实性。

---

## 2 Lean4证明

### 2.1 基本类型 (`BasicTypes.lean`)

使用Lean4重新实现基本类型定义。

### 2.2 资源安全 (`ResourceSafety.lean`)

线性类型与资源安全的对应证明。

---

## 3 TLA+规约

### 3.1 调度规约 (`Scheduling.tla`)

调度系统的时序逻辑规约。

---

## 4 构建与验证

### 4.1 Coq

```bash
# 安装Coq
opam install coq

# 编译验证
coqc coq/BasicTypes.v
coqc coq/ImageLayers.v
coqc coq/Functors.v
```

### 4.2 Lean4

```bash
# 安装Lean4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# 构建验证
lake build
```

### 4.3 TLA+

使用TLC模型检查器验证。

---

**返回**: [形式化理论](../09_形式化理论/README.md) | [形式语言视角](../README.md)
