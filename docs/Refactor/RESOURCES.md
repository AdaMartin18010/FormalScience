# 外部资源汇总 (External Resources)

> 本文档汇总了FormalScience项目相关的学习资源，包括书籍、课程、项目、论文和社区资源。

---

## 📚 推荐书籍

### 入门书籍

| 书名 | 作者 | 难度 | 说明 |
|-----|------|-----|------|
| **Theorem Proving in Lean 4** | Jeremy Avigad, Leonardo de Moura, et al. | ⭐ 初级 | Lean 4官方入门教程，必读书籍 |
| **Functional Programming in Lean** | David Thrane Christiansen | ⭐ 初级 | 函数式编程视角学习Lean |
| **The Hitchhiker's Guide to Logical Verification** | Anne Baanen, et al. | ⭐⭐ 初中 | 逻辑验证的实用指南 |

### 进阶书籍

| 书名 | 作者 | 难度 | 说明 |
|-----|------|-----|------|
| **Mathematics in Lean** | Kevin Buzzard, et al. | ⭐⭐⭐ 中级 | 使用Lean进行数学证明 |
| **The Mechanics of Proof** | Heather Macbeth | ⭐⭐⭐ 中级 | 本科数学的形式化方法 |
| **Programming Language Foundations in Agda** | Philip Wadler, et al. | ⭐⭐⭐ 中级 | PLT相关的类型论内容 |
| **Type Theory and Formal Proof** | Rob Nederpelt, Herman Geuvers | ⭐⭐⭐⭐ 高级 | 类型论和形式证明的理论基础 |

### 理论参考

| 书名 | 作者 | 难度 | 说明 |
|-----|------|-----|------|
| **Homotopy Type Theory** | The Univalent Foundations Program | ⭐⭐⭐⭐ 高级 | HoTT圣经，同伦类型论 |
| **Software Foundations** | Benjamin Pierce, et al. | ⭐⭐⭐ 中级 | 基于Coq的软件基础系列 |
| **Certified Programming with Dependent Types** | Adam Chlipala | ⭐⭐⭐⭐ 高级 | Coq依赖类型编程 |

---

## 🎓 在线课程

### 视频课程

#### Lean相关

- **[Formalising Mathematics 2024](https://www.youtube.com/playlist?list=PLVZep5wTamMmqv14v7Slh-9Y2fOL1aEjM)** - Kevin Buzzard
  - 帝国理工大学的Lean数学形式化课程
  - 适合：有数学背景的学习者
  - 语言：英语

- **[Lean 4 Tutorials](https://www.youtube.com/@leanprovercommunity)** - Lean Community
  - 官方社区频道，包含各类教程
  - 适合：各级别学习者
  - 语言：英语

- **[Theorem Proving in Lean](https://leanprover-community.github.io/learn.html)**
  - 官方文档配套的讲解视频
  - 适合：初学者
  - 免费，随文档更新

#### 类型论与逻辑

- **[Category Theory](https://www.youtube.com/playlist?list=PLbgaMIhjbmEnaH_LTkxLI7FMa2HsnawM_)** - Bartosz Milewski
  - 范畴论入门经典
  - 适合：理解数学结构
  - 语言：英语

- **[Types Summer School](https://www.youtube.com/@typessummerschool367)**
  - 类型论暑期学校录像
  - 适合：深入学习类型论
  - 语言：英语

### 互动课程

| 课程 | 平台 | 说明 |
|-----|------|------|
| **Natural Number Game** | [nng4leanprover.github.io](https://nng4.leanprover.cn/) | Lean 4版本的加法游戏 |
| **The Proof Assistant Demystifier** | Lean社区 | 交互式Lean教程 |
| **Logic and Proof** | CMU | 逻辑与证明课程 |

### 大学课程材料

- **[CS 1112: Introduction to Mathematical Proof](https://www.cs.cornell.edu/courses/cs1112/2023sp/)** - Cornell
- **[6.042J Mathematics for Computer Science](https://ocw.mit.edu/courses/6-042j-mathematics-for-computer-science-fall-2010/)** - MIT OCW
- **[CS 2800: Discrete Structures](https://www.cs.cornell.edu/courses/cs2800/2023fa/)** - Cornell

---

## 🔬 开源项目

### Lean/Mathlib项目

| 项目 | 链接 | 说明 |
|-----|------|------|
| **mathlib4** | [github.com/leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) | Lean 4数学库，必学 |
| **lean4** | [github.com/leanprover/lean4](https://github.com/leanprover/lean4) | Lean 4编译器和核心库 |
| **std4** | [github.com/leanprover/std4](https://github.com/leanprover/std4) | 标准库扩展 |
| **ProofWidgets4** | [github.com/leanprover-community/ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4) | 交互式证明组件 |

### 形式化数学项目

| 项目 | 链接 | 说明 |
|-----|------|------|
| **Liquid Tensor Experiment** | [github.com/leanprover-community/lean-liquid](https://github.com/leanprover-community/lean-liquid) | 液体张量实验，Peter Scholze猜想 |
| **Fermat's Last Theorem** | [github.com/ImperialCollegeLondon/FLT](https://github.com/ImperialCollegeLondon/FLT) | 费马大定理形式化项目 |
| **Sphere Eversion** | [github.com/leanprover-community/sphere-eversion](https://github.com/leanprover-community/sphere-eversion) | 球面外翻问题 |
| **Perfectoid Spaces** | [github.com/leanprover-community/lean-perfectoid-spaces](https://github.com/leanprover-community/lean-perfectoid-spaces) | 完美oid空间 |

### 计算机科学形式化

| 项目 | 链接 | 说明 |
|-----|------|------|
| **iris** | [gitlab.mpi-sws.org/iris/iris](https://gitlab.mpi-sws.org/iris/iris) | 高阶并发分离逻辑 |
| **compcert** | [github.com/AbsInt/CompCert](https://github.com/AbsInt/CompCert) | 经过验证的C编译器 |
| **sel4** | [github.com/seL4/seL4](https://github.com/seL4/seL4) | 经过验证的操作系统内核 |
| **vellvm** | [github.com/vellvm/vellvm](https://github.com/vellvm/vellvm) | LLVM的形式化语义 |

### 教育项目

| 项目 | 链接 | 说明 |
|-----|------|------|
| **Natural Number Game** | [github.com/leanprover-community/NNG4](https://github.com/leanprover-community/NNG4) | 自然数游戏源码 |
| **Lean Game Server](https://github.com/leanprover-community/lean4game) | 交互式游戏框架 |
| **GlimpseOfLean](https://github.com/PatrickMassot/GlimpseOfLean) | Lean入门示例 |

---

## 📄 研究论文

### 基础理论

| 论文 | 作者 | 年份 | 主题 |
|-----|------|-----|------|
| **The Lean 4 Theorem Prover** | Leonardo de Moura, Sebastian Ullrich | 2021 | Lean 4系统介绍 |
| **Elaboration in Dependent Type Theory** | Leonardo de Moura, et al. | 2015 | 依赖类型细化 |
| **The Science of Better: The Engineered Proof** | Thomas Hales | 2017 | 形式化证明的工业应用 |

### Mathlib相关

| 论文 | 作者 | 年份 | 主题 |
|-----|------|-----|------|
| **A Lean Blueprint for Formal Mathematics** | Patrick Massot | 2023 | Mathlib项目组织方法 |
| **Maintaining a Library of Formal Mathematics** | The Mathlib Community | 2020 | Mathlib社区经验 |
| **Formalising the Krull Topology** | Mathematics in Lean | 2023 | 拓扑学形式化 |

### 形式化数学成果

| 论文 | 作者 | 年份 | 主题 |
|-----|------|-----|------|
| **Formalizing 100 Theorems** | Freek Wiedijk | 持续更新 | 100个重要定理的形式化状态 |
| **A Machine-Checked Proof of the Odd Order Theorem** | Georges Gonthier, et al. | 2013 | Feit-Thompson定理(Coq) |
| **Formal Proof of the Kepler Conjecture** | Thomas Hales, et al. | 2017 | 开普勒猜想证明 |

### 类型论与证明论

| 论文 | 作者 | 年份 | 主题 |
|-----|------|-----|------|
| **Homotopy Type Theory: An Introduction** | Steve Awodey | 2012 | HoTT导论 |
| **Type-Driven Development** | Edwin Brady | 2017 | 类型驱动开发 |
| **The Next 700 Programming Languages** | Peter Landin | 1966 | 编程语言设计经典 |

---

## 🌐 社区资源

### 官方资源

| 资源 | 链接 | 说明 |
|-----|------|------|
| **Lean官网** | [lean-lang.org](https://lean-lang.org/) | 官方网站和文档 |
| **Mathlib文档** | [leanprover-community.github.io/mathlib4_docs](https://leanprover-community.github.io/mathlib4_docs/) | API文档 |
| **Lean 4 GitHub](https://github.com/leanprover/lean4) | 源码仓库 |
| **Mathlib GitHub](https://github.com/leanprover-community/mathlib4) | 数学库仓库 |

### 讨论平台

| 平台 | 链接 | 说明 |
|-----|------|------|
| **Zulip Chat** | [leanprover.zulipchat.com](https://leanprover.zulipchat.com/) | 主要讨论平台，推荐加入 |
| **GitHub Discussions** | [github.com/leanprover/lean4/discussions](https://github.com/leanprover/lean4/discussions) | 技术讨论 |
| **Stack Overflow** | [stackoverflow.com/questions/tagged/lean](https://stackoverflow.com/questions/tagged/lean) | 问答社区 |
| **Reddit r/leanprover](https://www.reddit.com/r/leanprover/) | 非正式讨论 |

### 搜索工具

| 工具 | 链接 | 说明 |
|-----|------|------|
| **Loogle** | [loogle.lean-lang.org](https://loogle.lean-lang.org/) | 按类型签名搜索 |
| **Mathlib Search](https://leanprover-community.github.io/mathlib_docs/) | 文档搜索 |
| **Moogle** | [www.moogle.ai](https://www.moogle.ai/) | AI辅助搜索 |

### 博客与文章

- **[Xena Project Blog](https://xenaproject.wordpress.com/)** - Kevin Buzzard的博客
- **[Lean Blog](https://lean-lang.org/blog/)** - 官方博客
- **[The Mechanical Tally](https://blog.trailofbits.com/category/formal-methods/)** - 形式化方法

### 会议与活动

| 会议 | 说明 |
|-----|------|
| **Lean Together** | Lean年度会议 |
| **CPP (Certified Programs and Proofs)** | 形式化证明会议 |
| **ITP (Interactive Theorem Proving)** | 交互式定理证明 |
| **FroCoS/TABLEAUX** | 自动推理会议 |

### 社交媒体

- **Twitter/X**: @leanprover, @xenaproject
- **YouTube**: Lean Community, Kevin Buzzard
- **Mastodon**: #leanprover标签

---

## 🛠️ 开发工具

### IDE和编辑器

| 工具 | 支持 | 说明 |
|-----|------|------|
| **VS Code** | Lean 4 | 推荐IDE，功能最完善 |
| **Neovim** | Lean 4 | 通过lean.nvim插件 |
| **Emacs** | Lean 4 | 传统选择 |

### 辅助工具

| 工具 | 用途 |
|-----|------|
| **LeanInk** | 文学化编程 |
| **doc-gen4** | 文档生成 |
| **lake** | 构建系统 |
| **lean4-mode** | Emacs模式 |

---

## 📊 资源分类索引

### 按难度分级

**初级 (⭐)**

- Theorem Proving in Lean 4
- Natural Number Game
- Functional Programming in Lean

**中级 (⭐⭐⭐)**

- Mathematics in Lean
- The Mechanics of Proof
- Mathlib源码阅读

**高级 (⭐⭐⭐⭐)**

- Homotopy Type Theory
- Type Theory and Formal Proof
- 研究论文

### 按主题分类

**Lean学习**
→ 见[入门书籍](#入门书籍)和[Lean相关课程](#lean相关)

**数学形式化**
→ 见[形式化数学项目](#形式化数学项目)和[Mathlib相关论文](#mathlib相关)

**计算机科学**
→ 见[CS形式化项目](#计算机科学形式化)和[理论参考](#理论参考)

**类型论**
→ 见[类型论课程](#类型论与逻辑)和[类型论文](#类型论与证明论)

---

## 💡 学习路径建议

### 路径一：定理证明入门 (3-6个月)

```
1. 阅读《Theorem Proving in Lean 4》(2-4周)
   ↓
2. 完成Natural Number Game(1周)
   ↓
3. 阅读《Mathematics in Lean》相关章节(2-4周)
   ↓
4. 参与Mathlib小贡献(持续)
   ↓
5. 阅读研究论文(进阶)
```

### 路径二：函数式编程背景 (2-4个月)

```
1. 阅读《Functional Programming in Lean》(2-3周)
   ↓
2. 完成在线互动教程(1-2周)
   ↓
3. 学习《The Hitchhiker's Guide to Logical Verification》(2-4周)
   ↓
4. 实践项目开发
```

### 路径三：学术研究导向 (6-12个月)

```
1. 完成基础路径
   ↓
2. 深入阅读类型论书籍
   ↓
3. 学习《Homotopy Type Theory》
   ↓
4. 参与大型形式化项目
   ↓
5. 发表相关工作
```

---

> 📝 **最后更新**: 2024年
>
> 🔄 **维护**: 欢迎提交PR补充新资源
>
> ⚠️ **注意**: 部分链接可能随时间变化，如遇失效请在社区寻求帮助
