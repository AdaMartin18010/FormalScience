- --
topic: "术语表（Glossary）"
dependencies: []
status: "review"
author: "FormalScience Project"
date: "2026-04-12"
version: "1.0.0"
tags: ["递归", "类型", "形式化", "证明", "定理"]
category: "reference"
priority: "medium"
- --

# 术语表（Glossary）


- --

## 1. 📋 目录 {#-目录} {#-目录--目录}

- [术语表（Glossary）](#术语表glossary)
  - [📋 目录](#-目录)
  - [1 使用说明](#1-使用说明)
  - [2 A](#2-a)
    - [2.1 AGI（Artificial General Intelligence，通用人工智能）](#21-agiartificial-general-intelligence通用人工智能)
    - [2.2 ANI（Artificial Narrow Intelligence，狭义人工智能）](#22-aniartificial-narrow-intelligence狭义人工智能)
    - [2.3 ASI（Artificial Superintelligence，超级人工智能）](#23-asiartificial-superintelligence超级人工智能)
    - [2.4 Attention Mechanism（注意力机制）](#24-attention-mechanism注意力机制)
  - [3 B](#3-b)
    - [3.1 Bias-Variance Tradeoff（偏差-方差权衡）](#31-bias-variance-tradeoff偏差-方差权衡)
  - [4 C](#4-c)
    - [4.1 CFL（Context-Free Language，上下文无关语言）](#41-cflcontext-free-language上下文无关语言)
    - [4.2 Chomsky Hierarchy（乔姆斯基层次）](#42-chomsky-hierarchy乔姆斯基层次)
    - [4.3 Chinese Room Argument（中文房间论证）](#43-chinese-room-argument中文房间论证)
    - [4.4 Computability（可计算性）](#44-computability可计算性)
    - [4.5 Church-Turing Thesis（邱奇-图灵论题）](#45-church-turing-thesis邱奇-图灵论题)
    - [4.6 Cosine Similarity（余弦相似度）](#46-cosine-similarity余弦相似度)
  - [5 D](#5-d)
    - [5.1 Decidability（可判定性）](#51-decidability可判定性)
    - [5.2 Distributional Semantics（分布式语义学）](#52-distributional-semantics分布式语义学)
  - [6 E](#6-e)
    - [6.1 Embedding（嵌入）](#61-embedding嵌入)
    - [6.2 Emergent Abilities（涌现能力）](#62-emergent-abilities涌现能力)
  - [7 F](#7-f)
    - [7.1 Finite Automaton（有限自动机）](#71-finite-automaton有限自动机)
    - [7.2 FLOPs（Floating Point Operations）](#72-flopsfloating-point-operations)
  - [8 G](#8-g)
    - [8.1 Generalization（泛化）](#81-generalization泛化)
    - [8.2 Gold's Theorem（Gold定理）](#82-golds-theoremgold定理)
    - [8.3 GPU（Graphics Processing Unit）](#83-gpugraphics-processing-unit)
  - [9 H](#9-h)
    - [9.1 Halting Problem（停机问题）](#91-halting-problem停机问题)
  - [10 I](#10-i)
    - [10.1 In-context Learning（上下文学习）](#101-in-context-learning上下文学习)
    - [10.2 Inductive Bias（归纳偏置）](#102-inductive-bias归纳偏置)
  - [11 L](#11-l)
    - [11.1 LLM（Large Language Model，大语言模型）](#111-llmlarge-language-model大语言模型)
  - [12 M](#12-m)
    - [12.1 Multimodal（多模态）](#121-multimodal多模态)
  - [13 N](#13-n)
    - [13.1 Neurosymbolic AI（神经符号AI）](#131-neurosymbolic-ai神经符号ai)
    - [13.2 Neuromorphic Computing（神经形态计算）](#132-neuromorphic-computing神经形态计算)
    - [13.3 NP-Complete（NP完全）](#133-np-completenp完全)
  - [14 P](#14-p)
    - [14.1 P vs NP](#141-p-vs-np)
    - [14.2 PAC Learning（Probably Approximately Correct Learning）](#142-pac-learningprobably-approximately-correct-learning)
    - [14.3 Perplexity（困惑度）](#143-perplexity困惑度)
    - [14.4 Prompt（提示）](#144-prompt提示)
  - [15 Q](#15-q)
    - [15.1 Quantum Computing（量子计算）](#151-quantum-computing量子计算)
  - [16 R](#16-r)
    - [16.1 RE（Recursively Enumerable，递归可枚举）](#161-rerecursively-enumerable递归可枚举)
    - [16.2 REG（Regular Language，正则语言）](#162-regregular-language正则语言)
    - [16.3 RLHF（Reinforcement Learning from Human Feedback）](#163-rlhfreinforcement-learning-from-human-feedback)
    - [16.4 RNN（Recurrent Neural Network，循环神经网络）](#164-rnnrecurrent-neural-network循环神经网络)
  - [17 S](#17-s)
    - [17.1 Scaling Laws（缩放法则）](#171-scaling-laws缩放法则)
    - [17.2 Self-Attention（自注意力）](#172-self-attention自注意力)
    - [17.3 Semantic Space（语义空间）](#173-semantic-space语义空间)
    - [17.4 SNN（Spiking Neural Network，脉冲神经网络）](#174-snnspiking-neural-network脉冲神经网络)
  - [18 T](#18-t)
    - [18.1 Token](#181-token)
    - [18.2 Transformer](#182-transformer)
    - [18.3 Turing Completeness（图灵完备性）](#183-turing-completeness图灵完备性)
    - [18.4 Turing Machine（图灵机）](#184-turing-machine图灵机)
  - [19 U](#19-u)
    - [19.1 Universal Approximation Theorem（通用逼近定理）](#191-universal-approximation-theorem通用逼近定理)
    - [19.2 Undecidability（不可判定性）](#192-undecidability不可判定性)
  - [20 V](#20-v)
    - [20.1 VC Dimension（VC维）](#201-vc-dimensionvc维)
    - [20.2 Vector Space（向量空间）](#202-vector-space向量空间)
  - [21 W](#21-w)
    - [21.1 Word2Vec](#211-word2vec)
  - [22 Z](#22-z)
    - [22.1 Zero-shot Learning（零样本学习）](#221-zero-shot-learning零样本学习)
  - [23 中文术语](#23-中文术语)
    - [23.1 对齐问题（Alignment Problem）](#231-对齐问题alignment-problem)
    - [23.2 符号主义（Symbolicism）](#232-符号主义symbolicism)
    - [23.3 归纳偏置（Inductive Bias）](#233-归纳偏置inductive-bias)
    - [23.4 连接主义（Connectionism）](#234-连接主义connectionism)
    - [23.5 泛化（Generalization）](#235-泛化generalization)
    - [23.6 算力（Computing Power）](#236-算力computing-power)
    - [23.7 停机问题（Halting Problem）](#237-停机问题halting-problem)
    - [23.8 图灵机（Turing Machine）](#238-图灵机turing-machine)
    - [23.9 意识（Consciousness）](#239-意识consciousness)
    - [23.10 语义（Semantics）](#2310-语义semantics)
    - [23.11 正则语言（Regular Language）](#2311-正则语言regular-language)
    - [23.12 注意力机制（Attention Mechanism）](#2312-注意力机制attention-mechanism)
  - [24 缩略语索引](#24-缩略语索引)
  - [25 参考资料](#25-参考资料)
  - [导航 | Navigation](#导航--navigation)
  - [相关主题 | Related Topics](#相关主题--related-topics)
    - [25.1 辅助文档](#251-辅助文档)
    - [25.2 核心章节](#252-核心章节)

- --

## 1. 使用说明 {#使用说明} {#使用说明-使用说明}

本术语表收录《AI模型视角》项目中的核心术语，按字母顺序排列（中文拼音首字母），提供简明定义和相关章节链接。

- --

## 2. A {#a} {#a-a}

### 2 1 AGI（Artificial General Intelligence，通用人工智能） {#1-agiartificial-general-intell} {#1-agiartificial-general-intell}

- *定义**：具有人类级别通用智能的AI系统，能够跨领域学习、推理和迁移。

- *相关章节**：10.1_AGI_Pathways.md

- *参见**：ANI, ASI

- --

### 2 2 ANI（Artificial Narrow Intelligence，狭义人工智能） {#2-aniartificial-narrow-intelli} {#2-aniartificial-narrow-intelli}

- *定义**：仅在单一任务或领域具有智能的AI系统，当前所有AI都属于ANI。

- *相关章节**：10.1_AGI_Pathways.md

- *参见**：AGI

- --

### 2 3 ASI（Artificial Superintelligence，超级人工智能） {#3-asiartificial-superintellige} {#3-asiartificial-superintellige}

- *定义**：在所有领域都超越人类智能的AI系统。

- *相关章节**：10.1_AGI_Pathways.md

- *参见**：AGI

- --

### 2 4 Attention Mechanism（注意力机制） {#4-attention-mechanism注意力机制} {#4-attention-mechanism注意力机制-4-a}

- *定义**：Transformer的核心机制，通过计算查询-键-值三元组实现序列建模。

- *数学形式**：`Attention(Q, K, V) = softmax(QK^T / √d_k)V`

- *相关章节**：02.2_RNN_Transformer_Architecture.md, 02.4_Transformer_Architecture.md

- *参见**：Self-Attention, Multi-Head Attention

- --

## 3. B {#b} {#b-b}

### 3 1 Bias-Variance Tradeoff（偏差-方差权衡） {#1-bias-variance-tradeoff偏差-方差权} {#1-bias-variance-tradeoff偏差-方差权}

- *定义**：学习理论中的核心权衡，偏差高则欠拟合，方差高则过拟合。

- *相关章节**：05.4_Generalization_Theory.md

- *参见**：Overfitting, Underfitting

- --

## 4. C {#c} {#c-c}

### 4 1 CFL（Context-Free Language，上下文无关语言） {#1-cflcontext-free-language上下文无} {#1-cflcontext-free-language上下文无}

- *定义**：Chomsky层次第2级，由上下文无关文法生成，可由下推自动机识别。

- *例子**：括号匹配、算术表达式

- *相关章节**：01.3_Formal_Language_Classification.md, 08.2_Formal_Language_Perspective.md

- *参见**：Chomsky Hierarchy, PDA

- --

### 4 2 Chomsky Hierarchy（乔姆斯基层次） {#2-chomsky-hierarchy乔姆斯基层次} {#2-chomsky-hierarchy乔姆斯基层次-2-ch}

- *定义**：形式语言的四级分类：REG, CFL, CSL, RE。

- *相关章节**：01.3_Formal_Language_Classification.md

- *参见**：Formal Language

- --

### 4 3 Chinese Room Argument（中文房间论证） {#3-chinese-room-argument中文房间论证} {#3-chinese-room-argument中文房间论证-}

- *定义**：John Searle提出的哲学论证，质疑AI是否真正"理解"。

- *相关章节**：07.1_Chinese_Room_Argument.md, 07.3_Understanding_vs_Simulation.md

- *参见**：Understanding vs Simulation

- --

### 4 4 Computability（可计算性） {#4-computability可计算性} {#4-computability可计算性-4-computab}

- *定义**：某问题是否存在算法可以解决的性质。

- *相关章节**：01.1_Turing_Machine_Computability.md

- *参见**：Church-Turing Thesis, Decidability

- --

### 4 5 Church-Turing Thesis（邱奇-图灵论题） {#5-church-turing-thesis邱奇-图灵论题} {#5-church-turing-thesis邱奇-图灵论题-}

- *定义**：任何可以被有效计算的函数都可以被图灵机计算。

- *相关章节**：01.1_Turing_Machine_Computability.md

- *参见**：Turing Machine

- --

### 4 6 Cosine Similarity（余弦相似度） {#6-cosine-similarity余弦相似度} {#6-cosine-similarity余弦相似度-6-cos}

- *定义**：测量向量夹角余弦值的相似度度量，范围[-1, 1]。

- *公式**：`cos(θ) = (u·v) / (||u|| ||v||)`

- *相关章节**：04.4_Semantic_Similarity_Metrics.md

- *参见**：Embedding, Vector Space

- --

## 5. D {#d} {#d-d}

### 5 1 Decidability（可判定性） {#1-decidability可判定性} {#1-decidability可判定性-1-decidabil}

- *定义**：某问题是否存在算法总能给出正确答案（是/否）的性质。

- *相关章节**：01.4_Decidability_Halting_Problem.md

- *参见**：Halting Problem, Undecidability

- --

### 5 2 Distributional Semantics（分布式语义学） {#2-distributional-semantics分布式语} {#2-distributional-semantics分布式语}

- *定义**："词的意义由其上下文决定"的语义学理论。

- *相关章节**：04.3_Distributional_Semantics.md

- *参见**：Word2Vec, Embedding

- --

## 6. E {#e} {#e-e}

### 6 1 Embedding（嵌入） {#1-embedding嵌入} {#1-embedding嵌入-1-embedding嵌入}

- *定义**：将离散符号（词、token）映射到连续向量空间的表示。

- *相关章节**：03.5_Embedding_Vector_Spaces.md, 04.1_Semantic_Vector_Spaces.md

- *参见**：Word2Vec, Vector Space

- --

### 6 2 Emergent Abilities（涌现能力） {#2-emergent-abilities涌现能力} {#2-emergent-abilities涌现能力-2-eme}

- *定义**：大模型在规模增长到一定程度后突然出现的新能力。

- *相关章节**：10.1_AGI_Pathways.md

- *参见**：Scaling Laws

- --

## 7. F {#f} {#f-f}

### 7 1 Finite Automaton（有限自动机） {#1-finite-automaton有限自动机} {#1-finite-automaton有限自动机-1-fini}

- *定义**：识别正则语言的最简单计算模型。

- *类型**：DFA（确定性）、NFA（非确定性）

- *相关章节**：01.2_Computational_Models_Hierarchy.md

- *参见**：Regular Language

- --

### 7 2 FLOPs（Floating Point Operations） {#2-flopsfloating-point-operatio} {#2-flopsfloating-point-operatio}

- *定义**：浮点运算次数，衡量计算量的单位。

- *相关章节**：08.3_Resource_Bounded_Computation.md, 09.4_Computing_Power_as_Resource.md

- *参见**：算力, GPU

- --

## 8. G {#g} {#g-g}

### 8 1 Generalization（泛化） {#1-generalization泛化} {#1-generalization泛化-1-generaliz}

- *定义**：模型在未见过的数据上表现良好的能力。

- *相关章节**：05.4_Generalization_Theory.md

- *参见**：Overfitting, Test Error

- --

### 8 2 Gold's Theorem（Gold定理） {#2-golds-theoremgold定理} {#2-golds-theoremgold定理-2-golds-}

- *定义**：超有限语言类（包括CFL、CSL、RE）无法从正例中可识别学习。

- *相关章节**：05.2_Gold_Learnability_Theory.md

- *参见**：Learnability

- --

### 8 3 GPU（Graphics Processing Unit） {#3-gpugraphics-processing-unit} {#3-gpugraphics-processing-unit-}

- *定义**：图形处理单元，现代AI训练和推理的核心硬件。

- *相关章节**：09.3_Computing_Infrastructure.md, 09.5_Data_Center_AI_Factory.md

- *参见**：算力, TPU

- --

## 9. H {#h} {#h-h}

### 9 1 Halting Problem（停机问题） {#1-halting-problem停机问题} {#1-halting-problem停机问题-1-haltin}

- *定义**：判定任意程序是否会停机的问题，证明为不可判定。

- *相关章节**：01.4_Decidability_Halting_Problem.md

- *参见**：Undecidability, Turing Machine

- --

## 10. I {#i} {#i-i}

### 10 1 In-context Learning（上下文学习） {#1-in-context-learning上下文学习} {#1-in-context-learning上下文学习-1-i}

- *定义**：大语言模型在推理时从提示中的示例学习，无需更新参数。

- *相关章节**：03.3_Transformer_LLM_Theory.md

- *参见**：Few-shot Learning, Prompt

- --

### 10 2 Inductive Bias（归纳偏置） {#2-inductive-bias归纳偏置} {#2-inductive-bias归纳偏置-2-inducti}

- *定义**：学习算法对未见数据做出预测时的假设倾向。

- *相关章节**：05.5_Inductive_Bias.md

- *参见**：Prior Knowledge

- --

## 11. L {#l} {#l-l}

### 11 1 LLM（Large Language Model，大语言模型） {#1-llmlarge-language-model大语言模型} {#1-llmlarge-language-model大语言模型}

- *定义**：参数量在数百亿以上的语言模型，如GPT-4、Claude等。

- *相关章节**：03.3_Transformer_LLM_Theory.md

- *参见**：Transformer, Token

- --

## 12. M {#m} {#m-m}

### 12 1 Multimodal（多模态） {#1-multimodal多模态} {#1-multimodal多模态-1-multimodal多模}

- *定义**：处理多种数据类型（文本、图像、音频等）的AI系统。

- *相关章节**：04.5_Multimodal_Semantic_Integration.md

- *参见**：CLIP, GPT-4V

- --

## 13. N {#n} {#n-n}

### 13 1 Neurosymbolic AI（神经符号AI） {#1-neurosymbolic-ai神经符号ai} {#1-neurosymbolic-ai神经符号ai-1-neu}

- *定义**：结合神经网络和符号推理的混合AI系统。

- *相关章节**：06.5_Hybrid_Neurosymbolic_Systems.md

- *参见**：Hybrid System

- --

### 13 2 Neuromorphic Computing（神经形态计算） {#2-neuromorphic-computing神经形态计算} {#2-neuromorphic-computing神经形态计算}

- *定义**：模拟生物神经系统的计算范式，使用脉冲神经网络。

- *相关章节**：10.3_Neuromorphic_Computing.md

- *参见**：SNN, Spiking Neural Network

- --

### 13 3 NP-Complete（NP完全） {#3-np-completenp完全} {#3-np-completenp完全-3-np-complet}

- *定义**：NP类中最难的问题，所有NP问题都可多项式时间归约到它。

- *相关章节**：01.5_Computational_Complexity_Classes.md

- *参见**：P vs NP, Complexity

- --

## 14. P {#p} {#p-p}

### 14 1 P vs NP {#1-p-vs-np} {#1-p-vs-np-1-p-vs-np}

- *定义**：计算机科学最重要的开放问题，问P（多项式时间）是否等于NP（非确定性多项式时间）。

- *相关章节**：01.5_Computational_Complexity_Classes.md

- *参见**：NP-Complete

- --

### 14 2 PAC Learning（Probably Approximately Correct Learning） {#2-pac-learningprobably-approxi} {#2-pac-learningprobably-approxi}

- *定义**：Valiant提出的学习理论框架，定义了"可学习"的形式化标准。

- *相关章节**：05.1_PAC_Learning_Framework.md

- *参见**：Sample Complexity, Learnability

- --

### 14 3 Perplexity（困惑度） {#3-perplexity困惑度} {#3-perplexity困惑度-3-perplexity困惑}

- *定义**：语言模型评估指标，测量模型对测试数据的"惊讶"程度。

- *公式**：`PPL = exp(-1/N * Σ log P(w_i | context))`

- *相关章节**：03.1_Statistical_Language_Models.md

- *参见**：Language Model

- --

### 14 4 Prompt（提示） {#4-prompt提示} {#4-prompt提示-4-prompt提示}

- *定义**：提供给大语言模型的输入文本，引导模型生成期望输出。

- *相关章节**：03.4_Token_Generation_Mechanisms.md

- *参见**：In-context Learning, Few-shot

- --

## 15. Q {#q} {#q-q}

### 15 1 Quantum Computing（量子计算） {#1-quantum-computing量子计算} {#1-quantum-computing量子计算-1-quan}

- *定义**：利用量子力学（叠加、纠缠）进行计算的范式。

- *相关章节**：10.2_Quantum_AI_Computing.md

- *参见**：Qubit, Quantum Machine Learning

- --

## 16. R {#r} {#r-r}

### 16 1 RE（Recursively Enumerable，递归可枚举） {#1-rerecursively-enumerable递归可枚} {#1-rerecursively-enumerable递归可枚}

- *定义**：Chomsky层次最高级，图灵机可识别的语言类。

- *相关章节**：01.3_Formal_Language_Classification.md

- *参见**：Turing Machine, Halting Problem

- --

### 16 2 REG（Regular Language，正则语言） {#2-regregular-language正则语言} {#2-regregular-language正则语言-2-re}

- *定义**：Chomsky层次第0级，有限自动机可识别的最简单语言类。

- *相关章节**：01.3_Formal_Language_Classification.md

- *参见**：Finite Automaton

- --

### 16 3 RLHF（Reinforcement Learning from Human Feedback） {#3-rlhfreinforcement-learning-f} {#3-rlhfreinforcement-learning-f}

- *定义**：从人类反馈中学习的强化学习方法，用于对齐AI行为。

- *相关章节**：07.6_AI_Alignment_Problem.md

- *参见**：Alignment, Fine-tuning

- --

### 16 4 RNN（Recurrent Neural Network，循环神经网络） {#4-rnnrecurrent-neural-network循} {#4-rnnrecurrent-neural-network循}

- *定义**：具有循环连接的神经网络，可处理序列数据。

- *相关章节**：02.2_RNN_Transformer_Architecture.md, 02.3_Turing_Completeness_Analysis.md

- *参见**：LSTM, GRU

- --

## 17. S {#s} {#s-s}

### 17 1 Scaling Laws（缩放法则） {#1-scaling-laws缩放法则} {#1-scaling-laws缩放法则-1-scaling-l}

- *定义**：描述模型性能如何随参数量、数据量、计算量变化的经验规律。

- *相关章节**：10.1_AGI_Pathways.md

- *参见**：Emergent Abilities

- --

### 17 2 Self-Attention（自注意力） {#2-self-attention自注意力} {#2-self-attention自注意力-2-self-at}

- *定义**：序列中每个位置关注所有位置的注意力机制。

- *相关章节**：02.4_Transformer_Architecture.md

- *参见**：Attention Mechanism, Transformer

- --

### 17 3 Semantic Space（语义空间） {#3-semantic-space语义空间} {#3-semantic-space语义空间-3-semanti}

- *定义**：高维向量空间，其中语义相近的概念距离接近。

- *相关章节**：04.1_Semantic_Vector_Spaces.md

- *参见**：Embedding, Distributional Semantics

- --

### 17 4 SNN（Spiking Neural Network，脉冲神经网络） {#4-snnspiking-neural-network脉冲神} {#4-snnspiking-neural-network脉冲神}

- *定义**：更接近生物神经元的网络模型，神经元通过脉冲（spike）通信。

- *相关章节**：10.3_Neuromorphic_Computing.md

- *参见**：Neuromorphic Computing

- --

## 18. T {#t} {#t-t}

### 18 1 Token {#1-token} {#1-token-1-token}

- *定义**：语言模型处理的基本单位，通常是子词或词片段。

- *相关章节**：03.4_Token_Generation_Mechanisms.md, 09.1_Token_as_Product.md

- *参见**：Tokenization, BPE

- --

### 18 2 Transformer {#2-transformer} {#2-transformer-2-transformer}

- *定义**：基于自注意力机制的神经网络架构，现代大语言模型的基础。

- *论文**：Vaswani et al. "Attention Is All You Need" (2017)

- *相关章节**：02.2_RNN_Transformer_Architecture.md, 02.4_Transformer_Architecture.md

- *参见**：Attention Mechanism, Self-Attention

- --

### 18 3 Turing Completeness（图灵完备性） {#3-turing-completeness图灵完备性} {#3-turing-completeness图灵完备性-3-t}

- *定义**：计算系统能够模拟图灵机的性质，即可计算所有可计算函数。

- *相关章节**：02.3_Turing_Completeness_Analysis.md

- *参见**：Turing Machine, Universal Computation

- --

### 18 4 Turing Machine（图灵机） {#4-turing-machine图灵机} {#4-turing-machine图灵机-4-turing-m}

- *定义**：Alan Turing提出的理论计算模型，现代计算机的数学模型。

- *组成**：无限纸带、读写头、状态转移函数

- *相关章节**：01.1_Turing_Machine_Computability.md

- *参见**：Church-Turing Thesis, Computability

- --

## 19. U {#u} {#u-u}

### 19 1 Universal Approximation Theorem（通用逼近定理） {#1-universal-approximation-theo} {#1-universal-approximation-theo}

- *定义**：单隐层前馈神经网络可以逼近任意连续函数。

- *相关章节**：02.5_Universal_Approximation_Theorem.md

- *参见**：Neural Network, Function Approximation

- --

### 19 2 Undecidability（不可判定性） {#2-undecidability不可判定性} {#2-undecidability不可判定性-2-undeci}

- *定义**：某问题不存在总能给出正确答案的算法。

- *例子**：停机问题、First-Order逻辑可满足性

- *相关章节**：01.4_Decidability_Halting_Problem.md

- *参见**：Halting Problem

- --

## 20. V {#v} {#v-v}

### 20 1 VC Dimension（VC维） {#1-vc-dimensionvc维} {#1-vc-dimensionvc维-1-vc-dimensi}

- *定义**：衡量假设空间复杂度的指标，与样本复杂度相关。

- *相关章节**：05.3_Sample_Complexity.md, 05.6_Statistical_Learning_Theory.md

- *参见**：Sample Complexity, PAC Learning

- --

### 20 2 Vector Space（向量空间） {#2-vector-space向量空间} {#2-vector-space向量空间-2-vector-sp}

- *定义**：数学结构，向量可进行加法和标量乘法运算。

- *AI应用**：嵌入、语义表示

- *相关章节**：04.1_Semantic_Vector_Spaces.md

- *参见**：Embedding, Semantic Space

- --

## 21. W {#w} {#w-w}

### 21 1 Word2Vec {#1-word2vec} {#1-word2vec-1-word2vec}

- *定义**：学习词嵌入的经典模型，包括CBOW和Skip-gram。

- *相关章节**：03.5_Embedding_Vector_Spaces.md, 04.3_Distributional_Semantics.md

- *参见**：Embedding, Distributional Semantics

- --

## 22. Z {#z} {#z-z}

### 22 1 Zero-shot Learning（零样本学习） {#1-zero-shot-learning零样本学习} {#1-zero-shot-learning零样本学习-1-ze}

- *定义**：模型在未见过任何示例的情况下完成任务的能力。

- *相关章节**：03.3_Transformer_LLM_Theory.md

- *参见**：Few-shot Learning, Transfer Learning

- --

## 23. 中文术语 {#中文术语} {#中文术语-中文术语}

### 23 1 对齐问题（Alignment Problem） {#1-对齐问题alignment-problem} {#1-对齐问题alignment-problem-1-对齐问题}

- *定义**：确保AI系统的目标和行为与人类价值一致的挑战。

- *相关章节**：07.6_AI_Alignment_Problem.md

- *参见**：RLHF, Value Alignment

- --

### 23 2 符号主义（Symbolicism） {#2-符号主义symbolicism} {#2-符号主义symbolicism-2-符号主义symbol}

- *定义**：基于符号操作和逻辑推理的AI范式。

- *相关章节**：06.1_Symbolic_AI_vs_Connectionist_AI.md

- *参见**：Connectionism, GOFAI

- --

### 23 3 归纳偏置（Inductive Bias） {#3-归纳偏置inductive-bias} {#3-归纳偏置inductive-bias-3-归纳偏置ind}

见 Inductive Bias

- --

### 23 4 连接主义（Connectionism） {#4-连接主义connectionism} {#4-连接主义connectionism-4-连接主义conn}

- *定义**：基于神经网络和分布式表示的AI范式。

- *相关章节**：06.1_Symbolic_AI_vs_Connectionist_AI.md

- *参见**：Symbolicism, Neural Network

- --

### 23 5 泛化（Generalization） {#5-泛化generalization} {#5-泛化generalization-5-泛化general}

见 Generalization

- --

### 23 6 算力（Computing Power） {#6-算力computing-power} {#6-算力computing-power-6-算力comput}

- *定义**：单位时间内可执行的计算操作数量。

- *度量**：FLOPs, FLOPS, GPU-hours

- *相关章节**：09.4_Computing_Power_as_Resource.md

- *参见**：FLOPs, GPU

- --

### 23 7 停机问题（Halting Problem） {#7-停机问题halting-problem} {#7-停机问题halting-problem-7-停机问题ha}

见 Halting Problem

- --

### 23 8 图灵机（Turing Machine） {#8-图灵机turing-machine} {#8-图灵机turing-machine-8-图灵机turin}

见 Turing Machine

- --

### 23 9 意识（Consciousness） {#9-意识consciousness} {#9-意识consciousness-9-意识consciou}

- *定义**：主观体验和自我意识的哲学概念。

- *AI相关**：AI是否能拥有意识？

- *相关章节**：07.2_Consciousness_in_AI.md, 10.4_AI_Consciousness_Research.md

- *参见**：Hard Problem of Consciousness

- --

### 23 10 语义（Semantics） {#10-语义semantics} {#10-语义semantics-10-语义semantics}

- *定义**：符号或表达式的意义。

- *相关章节**：第04章全部

- *参见**：Semantic Space, Distributional Semantics

- --

### 23 11 正则语言（Regular Language） {#11-正则语言regular-language} {#11-正则语言regular-language-11-正则语}

见 REG

- --

### 23 12 注意力机制（Attention Mechanism） {#12-注意力机制attention-mechanism} {#12-注意力机制attention-mechanism-12}

见 Attention Mechanism

- --

## 24. 缩略语索引 {#缩略语索引} {#缩略语索引-缩略语索引}

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

- --

## 25. 参考资料 {#参考资料} {#参考资料-参考资料}

完整定义和详细讨论请参阅各章节文档。

- --

## 27. 导航 | Navigation {#导航--navigation} {#导航--navigation-导航--navigation}

- *返回主页**: [← AI模型视角总览](./README.md)
- *相关文档**: [快速参考 →](./QUICK_REFERENCE.md) | [常见问题 →](./FAQ.md)
- *学习指南**: [学习路径 →](./LEARNING_PATHS.md)

- --

## 28. 相关主题 | Related Topics {#相关主题--related-topics} {#相关主题--related-topics-相关主题--rel}

### 25 1 辅助文档 {#1-辅助文档} {#1-辅助文档-1-辅助文档}

- [AI模型视角总览](./README.md)
- [完整索引](./00_Master_Index.md)
- [快速参考](./QUICK_REFERENCE.md)
- [学习路径](./LEARNING_PATHS.md)
- [常见问题](./FAQ.md)

### 25 2 核心章节 {#2-核心章节} {#2-核心章节-2-核心章节}

- [01 基础理论](./01_Foundational_Theory/01.1_Turing_Machine_Computability.md)
- [02 神经网络理论](./02_Neural_Network_Theory/02.1_Neural_Network_Foundations.md)
- [03 语言模型](./03_Language_Models/03.1_Statistical_Language_Models.md)
- [05 学习理论](./05_Learning_Theory/05.1_PAC_Learning_Framework.md)

- --

- *最后更新**：2025-10-25


- --

## 29. 关联网络 {#关联网络}

### 29.1 前向引用 {#前向引用}

> 本文档为以下文档提供基础：
> - [相关文档](./) (待补充)

### 29.2 后向引用 {#后向引用}

> 本文档依赖以下基础文档：
> - [基础文档](./) (待补充)

### 29.3 交叉链接 {#交叉链接}

> 相关主题：
> - [主题A](./) (待补充)
> - [主题B](./) (待补充)

- --

- 本文档由 FormalScience 文档规范化工具自动生成*
