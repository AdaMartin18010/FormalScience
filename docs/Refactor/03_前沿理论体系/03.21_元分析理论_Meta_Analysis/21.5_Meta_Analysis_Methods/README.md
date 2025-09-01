# 21.5 元分析方法 (Meta-Analysis Methods)

## 📋 模块概述

元分析方法是元分析理论的核心技术体系，包括效应量计算、异质性检验、发表偏倚检测、敏感性分析等统计方法。本模块为元分析的实施提供系统的方法论指导。

## 🏗️ 目录结构

```text
21.5_Meta_Analysis_Methods/
├── README.md                           # 模块导航
├── 21.5.1_Effect_Size_Calculation.md  # 效应量计算 ✅
├── 21.5.2_Heterogeneity_Analysis.md   # 异质性分析 ✅
├── 21.5.3_Publication_Bias.md         # 发表偏倚 ✅
└── 21.5.4_Sensitivity_Analysis.md     # 敏感性分析 ✅
```

## 🔬 核心理论

### 1. 效应量计算理论

**定义 1.1** (效应量)
效应量是衡量干预效果大小的标准化指标。

**定义 1.2** (标准化均数差)
标准化均数差：$d = \frac{\bar{X}_1 - \bar{X}_2}{s_p}$

**定理 1.1** (效应量标准化)
效应量标准化使得不同研究的结果可以比较。

### 2. 异质性分析理论

**定义 2.1** (异质性)
异质性是研究间效应量差异的程度。

**定义 2.2** (Q统计量)
Q统计量：$Q = \sum_{i=1}^{k} w_i(y_i - \bar{y})^2$

**定理 2.1** (异质性检验)
Q统计量服从自由度为k-1的卡方分布。

### 3. 发表偏倚理论

**定义 3.1** (发表偏倚)
发表偏倚是研究结果影响其发表可能性的现象。

**定义 3.2** (漏斗图)
漏斗图是检测发表偏倚的图形方法。

**定理 3.1** (发表偏倚影响)
发表偏倚会导致元分析结果偏倚。

### 4. 敏感性分析理论

**定义 4.1** (敏感性分析)
敏感性分析是评估元分析结果稳健性的方法。

**定义 4.2** (留一法)
留一法是逐个排除单个研究的敏感性分析方法。

**定理 4.1** (敏感性重要性)
敏感性分析有助于识别影响结果的关键研究。

## 📊 重构进度

### 已完成重构的子模块

✅ **21.5.1_Effect_Size_Calculation** - 效应量计算
✅ **21.5.2_Heterogeneity_Analysis** - 异质性分析
✅ **21.5.3_Publication_Bias** - 发表偏倚
✅ **21.5.4_Sensitivity_Analysis** - 敏感性分析

### 重构特色

1. **形式化语义体系**：为每个理论提供了严格的数学定义和符号表示
2. **多表征方式**：提供了图形、表格、数学、伪代码等多种表达方式
3. **Rust实现**：每个理论都有完整的Rust代码实现
4. **哲学性批判**：增加了深刻的哲学反思和批判

## 🧠 哲学性批判与展望

### 本体论反思

**元分析方法的哲学本质**：
元分析方法体现了人类对知识整合和真理追求的哲学思考。

**统计方法的实在性**：
统计方法是否真实反映了客观世界的规律。

### 认识论批判

**方法选择的哲学问题**：
如何选择最合适的元分析方法。

**不确定性的认知**：
人类如何理解和处理统计不确定性。

### 社会影响分析

**科学决策的价值**：
元分析方法为科学决策提供了重要依据。

**社会责任感**：
元分析方法需要考虑其社会影响和伦理责任。

## 📚 参考文献

1. Borenstein, M., et al. *Introduction to Meta-Analysis*. Wiley, 2009.
2. Higgins, J. P. T., & Green, S. *Cochrane Handbook for Systematic Reviews of Interventions*. Wiley, 2011.
3. Egger, M., et al. *Bias in meta-analysis detected by a simple, graphical test*. BMJ, 1997.
4. Sterne, J. A. C., et al. *Recommendations for examining and interpreting funnel plot asymmetry in meta-analyses of randomised controlled trials*. BMJ, 2011.
