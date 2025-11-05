# 21.3 证据合成 (Evidence Synthesis)

## 📋 模块概述

证据合成是元分析理论的核心，是将多个独立研究的结果进行统计整合，形成更可靠、更精确的总体估计的过程。本模块涵盖固定效应模型、随机效应模型、网络元分析等核心方法。

## 🏗️ 目录结构

```text
21.3_Evidence_Synthesis/
├── README.md                           # 模块导航
├── 21.3.1_Fixed_Effect_Model.md       # 固定效应模型 ✅
├── 21.3.2_Random_Effect_Model.md      # 随机效应模型 ✅
├── 21.3.3_Network_Meta_Analysis.md    # 网络元分析 ✅
└── 21.3.4_Bayesian_Meta_Analysis.md   # 贝叶斯元分析 ✅
```

## 🔬 核心理论

### 1. 固定效应模型理论

**定义 1.1** (固定效应模型)
固定效应模型假设所有研究共享一个共同的真实效应量：$\theta_i = \theta$

**定义 1.2** (加权平均)
固定效应模型的效应量估计：$\hat{\theta} = \frac{\sum_{i=1}^{k} w_i y_i}{\sum_{i=1}^{k} w_i}$

**定理 1.1** (同质性假设)
固定效应模型要求研究间效应量同质。

### 2. 随机效应模型理论

**定义 2.1** (随机效应模型)
随机效应模型允许研究间效应量存在异质性：$\theta_i \sim N(\mu, \tau^2)$

**定义 2.2** (异质性参数)
$\tau^2$表示研究间效应量的方差。

**定理 2.1** (异质性检验)
Q统计量用于检验研究间异质性。

### 3. 网络元分析理论

**定义 3.1** (网络元分析)
网络元分析同时比较多个干预措施，利用直接和间接证据。

**定义 3.2** (一致性假设)
直接和间接证据之间的一致性假设。

**定理 3.1** (证据整合)
网络元分析可以整合直接和间接证据。

### 4. 贝叶斯元分析理论

**定义 4.1** (贝叶斯元分析)
贝叶斯元分析使用贝叶斯统计方法进行元分析。

**定义 4.2** (先验分布)
先验分布反映对效应量的先验信念。

**定理 4.1** (后验分布)
后验分布结合先验信息和数据信息。

## 📊 重构进度

### 已完成重构的子模块

✅ **21.3.1_Fixed_Effect_Model** - 固定效应模型
✅ **21.3.2_Random_Effect_Model** - 随机效应模型
✅ **21.3.3_Network_Meta_Analysis** - 网络元分析
✅ **21.3.4_Bayesian_Meta_Analysis** - 贝叶斯元分析

### 重构特色

1. **形式化语义体系**：为每个理论提供了严格的数学定义和符号表示
2. **多表征方式**：提供了图形、表格、数学、伪代码等多种表达方式
3. **Rust实现**：每个理论都有完整的Rust代码实现
4. **哲学性批判**：增加了深刻的哲学反思和批判

## 🧠 哲学性批判与展望

### 本体论反思

**证据合成的哲学本质**：
证据合成体现了人类对真理和知识的哲学追求。

**统计模型的实在性**：
统计模型是否真实反映了客观世界的规律。

### 认识论批判

**模型选择的哲学问题**：
如何选择最合适的统计模型。

**不确定性的认知**：
人类如何理解和处理统计不确定性。

### 社会影响分析

**科学决策的价值**：
证据合成为科学决策提供了重要依据。

**社会责任感**：
证据合成需要考虑其社会影响和伦理责任。

## 📚 参考文献

1. Borenstein, M., et al. _Introduction to Meta-Analysis_. Wiley, 2009.
2. Higgins, J. P. T., & Green, S. _Cochrane Handbook for Systematic Reviews of Interventions_. Wiley, 2011.
3. Salanti, G. _Indirect and mixed-treatment comparison, network, or multiple-treatments meta-analysis_. Statistics in Medicine, 2012.
4. Spiegelhalter, D. J., et al. _Bayesian approaches to clinical trials and health-care evaluation_. Wiley, 2004.
