# 术语表（Glossary）


---

## 📋 目录

- [术语表（Glossary）](#术语表glossary)
  - [📋 目录](#-目录)
  - [使用说明](#使用说明)
  - [A](#a)
    - [AGI（Artificial General Intelligence，通用人工智能）](#agiartificial-general-intelligence通用人工智能)
    - [ANI（Artificial Narrow Intelligence，狭义人工智能）](#aniartificial-narrow-intelligence狭义人工智能)
    - [ASI（Artificial Superintelligence，超级人工智能）](#asiartificial-superintelligence超级人工智能)
    - [Attention Mechanism（注意力机制）](#attention-mechanism注意力机制)
  - [B](#b)
    - [Bias-Variance Tradeoff（偏差-方差权衡）](#bias-variance-tradeoff偏差-方差权衡)
  - [C](#c)
    - [CFL（Context-Free Language，上下文无关语言）](#cflcontext-free-language上下文无关语言)
    - [Chomsky Hierarchy（乔姆斯基层次）](#chomsky-hierarchy乔姆斯基层次)
    - [Chinese Room Argument（中文房间论证）](#chinese-room-argument中文房间论证)
    - [Computability（可计算性）](#computability可计算性)
    - [Church-Turing Thesis（邱奇-图灵论题）](#church-turing-thesis邱奇-图灵论题)
    - [Cosine Similarity（余弦相似度）](#cosine-similarity余弦相似度)
  - [D](#d)
    - [Decidability（可判定性）](#decidability可判定性)
    - [Distributional Semantics（分布式语义学）](#distributional-semantics分布式语义学)
  - [E](#e)
    - [Embedding（嵌入）](#embedding嵌入)
    - [Emergent Abilities（涌现能力）](#emergent-abilities涌现能力)
  - [F](#f)
    - [Finite Automaton（有限自动机）](#finite-automaton有限自动机)
    - [FLOPs（Floating Point Operations）](#flopsfloating-point-operations)
  - [G](#g)
    - [Generalization（泛化）](#generalization泛化)
    - [Gold's Theorem（Gold定理）](#golds-theoremgold定理)
    - [GPU（Graphics Processing Unit）](#gpugraphics-processing-unit)
  - [H](#h)
    - [Halting Problem（停机问题）](#halting-problem停机问题)
  - [I](#i)
    - [In-context Learning（上下文学习）](#in-context-learning上下文学习)
    - [Inductive Bias（归纳偏置）](#inductive-bias归纳偏置)
  - [L](#l)
    - [LLM（Large Language Model，大语言模型）](#llmlarge-language-model大语言模型)
  - [M](#m)
    - [Multimodal（多模态）](#multimodal多模态)
  - [N](#n)
    - [Neurosymbolic AI（神经符号AI）](#neurosymbolic-ai神经符号ai)
    - [Neuromorphic Computing（神经形态计算）](#neuromorphic-computing神经形态计算)
    - [NP-Complete（NP完全）](#np-completenp完全)
  - [P](#p)
    - [P vs NP](#p-vs-np)
    - [PAC Learning（Probably Approximately Correct Learning）](#pac-learningprobably-approximately-correct-learning)
    - [Perplexity（困惑度）](#perplexity困惑度)
    - [Prompt（提示）](#prompt提示)
  - [Q](#q)
    - [Quantum Computing（量子计算）](#quantum-computing量子计算)
  - [R](#r)
    - [RE（Recursively Enumerable，递归可枚举）](#rerecursively-enumerable递归可枚举)
    - [REG（Regular Language，正则语言）](#regregular-language正则语言)
    - [RLHF（Reinforcement Learning from Human Feedback）](#rlhfreinforcement-learning-from-human-feedback)
    - [RNN（Recurrent Neural Network，循环神经网络）](#rnnrecurrent-neural-network循环神经网络)
  - [S](#s)
    - [Scaling Laws（缩放法则）](#scaling-laws缩放法则)
    - [Self-Attention（自注意力）](#self-attention自注意力)
    - [Semantic Space（语义空间）](#semantic-space语义空间)
    - [SNN（Spiking Neural Network，脉冲神经网络）](#snnspiking-neural-network脉冲神经网络)
  - [T](#t)
    - [Token](#token)
    - [Transformer](#transformer)
    - [Turing Completeness（图灵完备性）](#turing-completeness图灵完备性)
    - [Turing Machine（图灵机）](#turing-machine图灵机)
  - [U](#u)
    - [Universal Approximation Theorem（通用逼近定理）](#universal-approximation-theorem通用逼近定理)
    - [Undecidability（不可判定性）](#undecidability不可判定性)
  - [V](#v)
    - [VC Dimension（VC维）](#vc-dimensionvc维)
    - [Vector Space（向量空间）](#vector-space向量空间)
  - [W](#w)
    - [Word2Vec](#word2vec)
  - [Z](#z)
    - [Zero-shot Learning（零样本学习）](#zero-shot-learning零样本学习)
  - [中文术语](#中文术语)
    - [对齐问题（Alignment Problem）](#对齐问题alignment-problem)
    - [符号主义（Symbolicism）](#符号主义symbolicism)
    - [归纳偏置（Inductive Bias）](#归纳偏置inductive-bias)
    - [连接主义（Connectionism）](#连接主义connectionism)
    - [泛化（Generalization）](#泛化generalization)
    - [算力（Computing Power）](#算力computing-power)
    - [停机问题（Halting Problem）](#停机问题halting-problem)
    - [图灵机（Turing Machine）](#图灵机turing-machine)
    - [意识（Consciousness）](#意识consciousness)
    - [语义（Semantics）](#语义semantics)
    - [正则语言（Regular Language）](#正则语言regular-language)
    - [注意力机制（Attention Mechanism）](#注意力机制attention-mechanism)
  - [缩略语索引](#缩略语索引)
  - [参考资料](#参考资料)
  - [导航 | Navigation](#导航--navigation)
  - [相关主题 | Related Topics](#相关主题--related-topics)
    - [辅助文档](#辅助文档)
    - [核心章节](#核心章节)

---

## 使用说明

本术语表收录《AI模型视角》项目中的核心术语，按字母顺序排列（中文拼音首字母），提供简明定义和相关章节链接。

---

## A

### AGI（Artificial General Intelligence，通用人工智能）

**定义**：具有人类级别通用智能的AI系统，能够跨领域学习、推理和迁移。

**相关章节**：10.1_AGI_Pathways.md

**参见**：ANI, ASI

---

### ANI（Artificial Narrow Intelligence，狭义人工智能）

**定义**：仅在单一任务或领域具有智能的AI系统，当前所有AI都属于ANI。

**相关章节**：10.1_AGI_Pathways.md

**参见**：AGI

---

### ASI（Artificial Superintelligence，超级人工智能）

**定义**：在所有领域都超越人类智能的AI系统。

**相关章节**：10.1_AGI_Pathways.md

**参见**：AGI

---

### Attention Mechanism（注意力机制）

**定义**：Transformer的核心机制，通过计算查询-键-值三元组实现序列建模。

**数学形式**：`Attention(Q, K, V) = softmax(QK^T / √d_k)V`

**相关章节**：02.2_RNN_Transformer_Architecture.md, 02.4_Transformer_Architecture.md

**参见**：Self-Attention, Multi-Head Attention

---

## B

### Bias-Variance Tradeoff（偏差-方差权衡）

**定义**：学习理论中的核心权衡，偏差高则欠拟合，方差高则过拟合。

**相关章节**：05.4_Generalization_Theory.md

**参见**：Overfitting, Underfitting

---

## C

### CFL（Context-Free Language，上下文无关语言）

**定义**：Chomsky层次第2级，由上下文无关文法生成，可由下推自动机识别。

**例子**：括号匹配、算术表达式

**相关章节**：01.3_Formal_Language_Classification.md, 08.2_Formal_Language_Perspective.md

**参见**：Chomsky Hierarchy, PDA

---

### Chomsky Hierarchy（乔姆斯基层次）

**定义**：形式语言的四级分类：REG, CFL, CSL, RE。

**相关章节**：01.3_Formal_Language_Classification.md

**参见**：Formal Language

---

### Chinese Room Argument（中文房间论证）

**定义**：John Searle提出的哲学论证，质疑AI是否真正"理解"。

**相关章节**：07.1_Chinese_Room_Argument.md, 07.3_Understanding_vs_Simulation.md

**参见**：Understanding vs Simulation

---

### Computability（可计算性）

**定义**：某问题是否存在算法可以解决的性质。

**相关章节**：01.1_Turing_Machine_Computability.md

**参见**：Church-Turing Thesis, Decidability

---

### Church-Turing Thesis（邱奇-图灵论题）

**定义**：任何可以被有效计算的函数都可以被图灵机计算。

**相关章节**：01.1_Turing_Machine_Computability.md

**参见**：Turing Machine

---

### Cosine Similarity（余弦相似度）

**定义**：测量向量夹角余弦值的相似度度量，范围[-1, 1]。

**公式**：`cos(θ) = (u·v) / (||u|| ||v||)`

**相关章节**：04.4_Semantic_Similarity_Metrics.md

**参见**：Embedding, Vector Space

---

## D

### Decidability（可判定性）

**定义**：某问题是否存在算法总能给出正确答案（是/否）的性质。

**相关章节**：01.4_Decidability_Halting_Problem.md

**参见**：Halting Problem, Undecidability

---

### Distributional Semantics（分布式语义学）

**定义**："词的意义由其上下文决定"的语义学理论。

**相关章节**：04.3_Distributional_Semantics.md

**参见**：Word2Vec, Embedding

---

## E

### Embedding（嵌入）

**定义**：将离散符号（词、token）映射到连续向量空间的表示。

**相关章节**：03.5_Embedding_Vector_Spaces.md, 04.1_Semantic_Vector_Spaces.md

**参见**：Word2Vec, Vector Space

---

### Emergent Abilities（涌现能力）

**定义**：大模型在规模增长到一定程度后突然出现的新能力。

**相关章节**：10.1_AGI_Pathways.md

**参见**：Scaling Laws

---

## F

### Finite Automaton（有限自动机）

**定义**：识别正则语言的最简单计算模型。

**类型**：DFA（确定性）、NFA（非确定性）

**相关章节**：01.2_Computational_Models_Hierarchy.md

**参见**：Regular Language

---

### FLOPs（Floating Point Operations）

**定义**：浮点运算次数，衡量计算量的单位。

**相关章节**：08.3_Resource_Bounded_Computation.md, 09.4_Computing_Power_as_Resource.md

**参见**：算力, GPU

---

## G

### Generalization（泛化）

**定义**：模型在未见过的数据上表现良好的能力。

**相关章节**：05.4_Generalization_Theory.md

**参见**：Overfitting, Test Error

---

### Gold's Theorem（Gold定理）

**定义**：超有限语言类（包括CFL、CSL、RE）无法从正例中可识别学习。

**相关章节**：05.2_Gold_Learnability_Theory.md

**参见**：Learnability

---

### GPU（Graphics Processing Unit）

**定义**：图形处理单元，现代AI训练和推理的核心硬件。

**相关章节**：09.3_Computing_Infrastructure.md, 09.5_Data_Center_AI_Factory.md

**参见**：算力, TPU

---

## H

### Halting Problem（停机问题）

**定义**：判定任意程序是否会停机的问题，证明为不可判定。

**相关章节**：01.4_Decidability_Halting_Problem.md

**参见**：Undecidability, Turing Machine

---

## I

### In-context Learning（上下文学习）

**定义**：大语言模型在推理时从提示中的示例学习，无需更新参数。

**相关章节**：03.3_Transformer_LLM_Theory.md

**参见**：Few-shot Learning, Prompt

---

### Inductive Bias（归纳偏置）

**定义**：学习算法对未见数据做出预测时的假设倾向。

**相关章节**：05.5_Inductive_Bias.md

**参见**：Prior Knowledge

---

## L

### LLM（Large Language Model，大语言模型）

**定义**：参数量在数百亿以上的语言模型，如GPT-4、Claude等。

**相关章节**：03.3_Transformer_LLM_Theory.md

**参见**：Transformer, Token

---

## M

### Multimodal（多模态）

**定义**：处理多种数据类型（文本、图像、音频等）的AI系统。

**相关章节**：04.5_Multimodal_Semantic_Integration.md

**参见**：CLIP, GPT-4V

---

## N

### Neurosymbolic AI（神经符号AI）

**定义**：结合神经网络和符号推理的混合AI系统。

**相关章节**：06.5_Hybrid_Neurosymbolic_Systems.md

**参见**：Hybrid System

---

### Neuromorphic Computing（神经形态计算）

**定义**：模拟生物神经系统的计算范式，使用脉冲神经网络。

**相关章节**：10.3_Neuromorphic_Computing.md

**参见**：SNN, Spiking Neural Network

---

### NP-Complete（NP完全）

**定义**：NP类中最难的问题，所有NP问题都可多项式时间归约到它。

**相关章节**：01.5_Computational_Complexity_Classes.md

**参见**：P vs NP, Complexity

---

## P

### P vs NP

**定义**：计算机科学最重要的开放问题，问P（多项式时间）是否等于NP（非确定性多项式时间）。

**相关章节**：01.5_Computational_Complexity_Classes.md

**参见**：NP-Complete

---

### PAC Learning（Probably Approximately Correct Learning）

**定义**：Valiant提出的学习理论框架，定义了"可学习"的形式化标准。

**相关章节**：05.1_PAC_Learning_Framework.md

**参见**：Sample Complexity, Learnability

---

### Perplexity（困惑度）

**定义**：语言模型评估指标，测量模型对测试数据的"惊讶"程度。

**公式**：`PPL = exp(-1/N * Σ log P(w_i | context))`

**相关章节**：03.1_Statistical_Language_Models.md

**参见**：Language Model

---

### Prompt（提示）

**定义**：提供给大语言模型的输入文本，引导模型生成期望输出。

**相关章节**：03.4_Token_Generation_Mechanisms.md

**参见**：In-context Learning, Few-shot

---

## Q

### Quantum Computing（量子计算）

**定义**：利用量子力学（叠加、纠缠）进行计算的范式。

**相关章节**：10.2_Quantum_AI_Computing.md

**参见**：Qubit, Quantum Machine Learning

---

## R

### RE（Recursively Enumerable，递归可枚举）

**定义**：Chomsky层次最高级，图灵机可识别的语言类。

**相关章节**：01.3_Formal_Language_Classification.md

**参见**：Turing Machine, Halting Problem

---

### REG（Regular Language，正则语言）

**定义**：Chomsky层次第0级，有限自动机可识别的最简单语言类。

**相关章节**：01.3_Formal_Language_Classification.md

**参见**：Finite Automaton

---

### RLHF（Reinforcement Learning from Human Feedback）

**定义**：从人类反馈中学习的强化学习方法，用于对齐AI行为。

**相关章节**：07.6_AI_Alignment_Problem.md

**参见**：Alignment, Fine-tuning

---

### RNN（Recurrent Neural Network，循环神经网络）

**定义**：具有循环连接的神经网络，可处理序列数据。

**相关章节**：02.2_RNN_Transformer_Architecture.md, 02.3_Turing_Completeness_Analysis.md

**参见**：LSTM, GRU

---

## S

### Scaling Laws（缩放法则）

**定义**：描述模型性能如何随参数量、数据量、计算量变化的经验规律。

**相关章节**：10.1_AGI_Pathways.md

**参见**：Emergent Abilities

---

### Self-Attention（自注意力）

**定义**：序列中每个位置关注所有位置的注意力机制。

**相关章节**：02.4_Transformer_Architecture.md

**参见**：Attention Mechanism, Transformer

---

### Semantic Space（语义空间）

**定义**：高维向量空间，其中语义相近的概念距离接近。

**相关章节**：04.1_Semantic_Vector_Spaces.md

**参见**：Embedding, Distributional Semantics

---

### SNN（Spiking Neural Network，脉冲神经网络）

**定义**：更接近生物神经元的网络模型，神经元通过脉冲（spike）通信。

**相关章节**：10.3_Neuromorphic_Computing.md

**参见**：Neuromorphic Computing

---

## T

### Token

**定义**：语言模型处理的基本单位，通常是子词或词片段。

**相关章节**：03.4_Token_Generation_Mechanisms.md, 09.1_Token_as_Product.md

**参见**：Tokenization, BPE

---

### Transformer

**定义**：基于自注意力机制的神经网络架构，现代大语言模型的基础。

**论文**：Vaswani et al. "Attention Is All You Need" (2017)

**相关章节**：02.2_RNN_Transformer_Architecture.md, 02.4_Transformer_Architecture.md

**参见**：Attention Mechanism, Self-Attention

---

### Turing Completeness（图灵完备性）

**定义**：计算系统能够模拟图灵机的性质，即可计算所有可计算函数。

**相关章节**：02.3_Turing_Completeness_Analysis.md

**参见**：Turing Machine, Universal Computation

---

### Turing Machine（图灵机）

**定义**：Alan Turing提出的理论计算模型，现代计算机的数学模型。

**组成**：无限纸带、读写头、状态转移函数

**相关章节**：01.1_Turing_Machine_Computability.md

**参见**：Church-Turing Thesis, Computability

---

## U

### Universal Approximation Theorem（通用逼近定理）

**定义**：单隐层前馈神经网络可以逼近任意连续函数。

**相关章节**：02.5_Universal_Approximation_Theorem.md

**参见**：Neural Network, Function Approximation

---

### Undecidability（不可判定性）

**定义**：某问题不存在总能给出正确答案的算法。

**例子**：停机问题、First-Order逻辑可满足性

**相关章节**：01.4_Decidability_Halting_Problem.md

**参见**：Halting Problem

---

## V

### VC Dimension（VC维）

**定义**：衡量假设空间复杂度的指标，与样本复杂度相关。

**相关章节**：05.3_Sample_Complexity.md, 05.6_Statistical_Learning_Theory.md

**参见**：Sample Complexity, PAC Learning

---

### Vector Space（向量空间）

**定义**：数学结构，向量可进行加法和标量乘法运算。

**AI应用**：嵌入、语义表示

**相关章节**：04.1_Semantic_Vector_Spaces.md

**参见**：Embedding, Semantic Space

---

## W

### Word2Vec

**定义**：学习词嵌入的经典模型，包括CBOW和Skip-gram。

**相关章节**：03.5_Embedding_Vector_Spaces.md, 04.3_Distributional_Semantics.md

**参见**：Embedding, Distributional Semantics

---

## Z

### Zero-shot Learning（零样本学习）

**定义**：模型在未见过任何示例的情况下完成任务的能力。

**相关章节**：03.3_Transformer_LLM_Theory.md

**参见**：Few-shot Learning, Transfer Learning

---

## 中文术语

### 对齐问题（Alignment Problem）

**定义**：确保AI系统的目标和行为与人类价值一致的挑战。

**相关章节**：07.6_AI_Alignment_Problem.md

**参见**：RLHF, Value Alignment

---

### 符号主义（Symbolicism）

**定义**：基于符号操作和逻辑推理的AI范式。

**相关章节**：06.1_Symbolic_AI_vs_Connectionist_AI.md

**参见**：Connectionism, GOFAI

---

### 归纳偏置（Inductive Bias）

见 Inductive Bias

---

### 连接主义（Connectionism）

**定义**：基于神经网络和分布式表示的AI范式。

**相关章节**：06.1_Symbolic_AI_vs_Connectionist_AI.md

**参见**：Symbolicism, Neural Network

---

### 泛化（Generalization）

见 Generalization

---

### 算力（Computing Power）

**定义**：单位时间内可执行的计算操作数量。

**度量**：FLOPs, FLOPS, GPU-hours

**相关章节**：09.4_Computing_Power_as_Resource.md

**参见**：FLOPs, GPU

---

### 停机问题（Halting Problem）

见 Halting Problem

---

### 图灵机（Turing Machine）

见 Turing Machine

---

### 意识（Consciousness）

**定义**：主观体验和自我意识的哲学概念。

**AI相关**：AI是否能拥有意识？

**相关章节**：07.2_Consciousness_in_AI.md, 10.4_AI_Consciousness_Research.md

**参见**：Hard Problem of Consciousness

---

### 语义（Semantics）

**定义**：符号或表达式的意义。

**相关章节**：第04章全部

**参见**：Semantic Space, Distributional Semantics

---

### 正则语言（Regular Language）

见 REG

---

### 注意力机制（Attention Mechanism）

见 Attention Mechanism

---

## 缩略语索引

- **AGI**: Artificial General Intelligence
- **ANI**: Artificial Narrow Intelligence
- **ASI**: Artificial Superintelligence
- **BPE**: Byte Pair Encoding
- **CFL**: Context-Free Language
- **CSL**: Context-Sensitive Language
- **DFA**: Deterministic Finite Automaton
- **GAN**: Generative Adversarial Network
- **GPU**: Graphics Processing Unit
- **GRU**: Gated Recurrent Unit
- **LLM**: Large Language Model
- **LSTM**: Long Short-Term Memory
- **NFA**: Nondeterministic Finite Automaton
- **NLP**: Natural Language Processing
- **PAC**: Probably Approximately Correct
- **PDA**: Pushdown Automaton
- **RE**: Recursively Enumerable
- **REG**: Regular Language
- **RLHF**: Reinforcement Learning from Human Feedback
- **RNN**: Recurrent Neural Network
- **SFT**: Supervised Fine-Tuning
- **SNN**: Spiking Neural Network
- **TPU**: Tensor Processing Unit
- **VAE**: Variational Autoencoder

---

## 参考资料

完整定义和详细讨论请参阅各章节文档。

---

## 导航 | Navigation

**返回主页**: [← AI模型视角总览](./README.md)
**相关文档**: [快速参考 →](./QUICK_REFERENCE.md) | [常见问题 →](./FAQ.md)
**学习指南**: [学习路径 →](./LEARNING_PATHS.md)

---

## 相关主题 | Related Topics

### 辅助文档

- [AI模型视角总览](./README.md)
- [完整索引](./00_Master_Index.md)
- [快速参考](./QUICK_REFERENCE.md)
- [学习路径](./LEARNING_PATHS.md)
- [常见问题](./FAQ.md)

### 核心章节

- [01 基础理论](./01_Foundational_Theory/01.1_Turing_Machine_Computability.md)
- [02 神经网络理论](./02_Neural_Network_Theory/02.1_Neural_Network_Foundations.md)
- [03 语言模型](./03_Language_Models/03.1_Statistical_Language_Models.md)
- [05 学习理论](./05_Learning_Theory/05.1_PAC_Learning_Framework.md)

---

**最后更新**：2025-10-25
