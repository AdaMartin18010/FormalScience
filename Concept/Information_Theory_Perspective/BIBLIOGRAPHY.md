- --
topic: "信息论多视角分析 - 完整参考文献"
dependencies: []
status: "review"
author: "FormalScience Project"
date: "2026-04-12"
version: "1.0.0"
tags: ["类型", "形式化", "证明", "定理", "算法"]
category: "theory"
priority: "medium"
- --

# 信息论多视角分析 - 完整参考文献

> **文档版本**: v1.0.0
> **最后更新**: 2025-10-27
> **文档规模**: 688行 | 信息论完整文献库
> **阅读建议**: 本文档收录信息论各领域的经典与前沿文献，建议分主题阅读

- --

## 1. 📋 目录 {#-目录} {#-目录--目录}

- [信息论多视角分析 - 完整参考文献](#信息论多视角分析---完整参考文献)
  - [📋 目录](#-目录)
  - [1 概述](#1-概述)
  - [1 . 经典信息论基础](#1--经典信息论基础)
    - [1.1 奠基性文献](#11-奠基性文献)
      - [1.1.1 Shannon, C. E. (1948)](#111-shannon-c-e-1948)
      - [1.1.2 Shannon, C. E. (1949)](#112-shannon-c-e-1949)
      - [1.1.3 Wiener, N. (1948)](#113-wiener-n-1948)
    - [1.2 经典教科书](#12-经典教科书)
      - [1.2.1 Cover, T. M., \& Thomas, J. A. (2006)](#121-cover-t-m--thomas-j-a-2006)
      - [1.2.2 MacKay, D. J. C. (2003)](#122-mackay-d-j-c-2003)
      - [1.2.3 Gallager, R. G. (1968)](#123-gallager-r-g-1968)
  - [2 . 量子信息论](#2--量子信息论)
    - [2.1 奠基性文献](#21-奠基性文献)
      - [2.1.1 Nielsen, M. A., \& Chuang, I. L. (2010)](#211-nielsen-m-a--chuang-i-l-2010)
      - [2.1.2 Wilde, M. M. (2013)](#212-wilde-m-m-2013)
    - [2.2 重要研究论文](#22-重要研究论文)
      - [2.2.1 Preskill, J. (2018)](#221-preskill-j-2018)
      - [2.2.2 Shor, P. W. (1994)](#222-shor-p-w-1994)
  - [3 . 语义信息论](#3--语义信息论)
    - [3.1 经典文献](#31-经典文献)
      - [3.1.1 Bar-Hillel, Y., \& Carnap, R. (1953)](#311-bar-hillel-y--carnap-r-1953)
      - [3.1.2 Floridi, L. (2004)](#312-floridi-l-2004)
    - [3.2 现代发展](#32-现代发展)
      - [3.2.1 Floridi, L. (2011)](#321-floridi-l-2011)
  - [4 . 生物信息论](#4--生物信息论)
    - [4.1 经典文献](#41-经典文献)
      - [4.1.1 Eigen, M. (1971)](#411-eigen-m-1971)
      - [4.1.2 Maynard Smith, J. (2000)](#412-maynard-smith-j-2000)
    - [4.2 现代发展](#42-现代发展)
      - [4.2.1 Adami, C. (2016)](#421-adami-c-2016)
  - [5 . 算法复杂度理论](#5--算法复杂度理论)
    - [5.1 经典文献](#51-经典文献)
      - [5.1.1 Kolmogorov, A. N. (1965)](#511-kolmogorov-a-n-1965)
      - [5.1.2 Solomonoff, R. J. (1964)](#512-solomonoff-r-j-1964)
    - [5.2 现代发展](#52-现代发展)
      - [5.2.1 Li, M., \& Vitányi, P. (2019)](#521-li-m--vitányi-p-2019)
  - [6 . 热力学信息论](#6--热力学信息论)
    - [6.1 经典文献](#61-经典文献)
      - [6.1.1 Landauer, R. (1961)](#611-landauer-r-1961)
      - [6.1.2 Bennett, C. H. (1982)](#612-bennett-c-h-1982)
    - [6.2 现代发展](#62-现代发展)
      - [6.2.1 Parrondo, J. M. R., Horowitz, J. M., \& Sagawa, T. (2015)](#621-parrondo-j-m-r-horowitz-j-m--sagawa-t-2015)
  - [7 . 几何信息论](#7--几何信息论)
    - [7.1 经典文献](#71-经典文献)
      - [7.1.1 Rao, C. R. (1945)](#711-rao-c-r-1945)
      - [7.1.2 Amari, S. (1985)](#712-amari-s-1985)
    - [7.2 现代发展](#72-现代发展)
      - [7.2.1 Amari, S. (2016)](#721-amari-s-2016)
  - [8 . 网络信息论](#8--网络信息论)
    - [8.1 经典文献](#81-经典文献)
      - [8.1.1 Ahlswede, R., Cai, N., Li, S. Y. R., \& Yeung, R. W. (2000)](#811-ahlswede-r-cai-n-li-s-y-r--yeung-r-w-2000)
      - [8.1.2 Cover, T. M., \& El Gamal, A. (1979)](#812-cover-t-m--el-gamal-a-1979)
    - [8.2 现代发展](#82-现代发展)
      - [8.2.1 El Gamal, A., \& Kim, Y. H. (2011)](#821-el-gamal-a--kim-y-h-2011)
  - [9 . 人工智能与信息论](#9--人工智能与信息论)
    - [9.1 经典文献](#91-经典文献)
      - [9.1.1 Tishby, N., Pereira, F. C., \& Bialek, W. (1999)](#911-tishby-n-pereira-f-c--bialek-w-1999)
      - [9.1.2 Alemi, A. A., Fischer, I., Dillon, J. V., \& Murphy, K. (2017)](#912-alemi-a-a-fischer-i-dillon-j-v--murphy-k-2017)
    - [9.2 现代发展](#92-现代发展)
      - [9.2.1 Belghazi, M. I., Baratin, A., Rajeswar, S., Ozair, S., Bengio, Y., Courville, A., \& Hjelm, R. D. (2018)](#921-belghazi-m-i-baratin-a-rajeswar-s-ozair-s-bengio-y-courville-a--hjelm-r-d-2018)
  - [10 . 哲学与信息论](#10--哲学与信息论)
    - [10.1 经典文献](#101-经典文献)
      - [10.1.1 Dretske, F. I. (1981)](#1011-dretske-f-i-1981)
      - [10.1.2 Floridi, L. (2013)](#1012-floridi-l-2013)
    - [10.2 现代发展](#102-现代发展)
      - [10.2.1 Floridi, L. (2019)](#1021-floridi-l-2019)
  - [11 . 应用领域](#11--应用领域)
    - [11.1 通信系统](#111-通信系统)
      - [11.1.1 Proakis, J. G., \& Salehi, M. (2008)](#1111-proakis-j-g--salehi-m-2008)
      - [11.1.2 Tse, D., \& Viswanath, P. (2005)](#1112-tse-d--viswanath-p-2005)
    - [11.2 数据压缩](#112-数据压缩)
      - [11.2.1 Salomon, D. (2007)](#1121-salomon-d-2007)
      - [11.2.2 Sayood, K. (2017)](#1122-sayood-k-2017)
    - [11.3 机器学习](#113-机器学习)
      - [11.3.1 Murphy, K. P. (2012)](#1131-murphy-k-p-2012)
      - [11.3.2 Goodfellow, I., Bengio, Y., \& Courville, A. (2016)](#1132-goodfellow-i-bengio-y--courville-a-2016)
  - [12 . 前沿研究](#12--前沿研究)
    - [12.1 量子机器学习](#121-量子机器学习)
      - [12.1.1 Biamonte, J., Wittek, P., Pancotti, N., Rebentrost, P., Wiebe, N., \& Lloyd, S. (2017)](#1211-biamonte-j-wittek-p-pancotti-n-rebentrost-p-wiebe-n--lloyd-s-2017)
    - [12.2 信息论与生物学](#122-信息论与生物学)
      - [12.2.1 Adami, C. (2012)](#1221-adami-c-2012)
    - [12.3 信息论与社会科学](#123-信息论与社会科学)
      - [12.3.1 Cover, T. M., \& Thomas, J. A. (2006)1](#1231-cover-t-m--thomas-j-a-20061)
  - [13 . 在线资源](#13--在线资源)
    - [13.1 权威网站](#131-权威网站)
      - [13.1.1 Wikipedia - Information Theory](#1311-wikipedia---information-theory)
      - [13.1.2 IEEE Information Theory Society](#1312-ieee-information-theory-society)
    - [13.2 学术数据库](#132-学术数据库)
      - [13.2.1 IEEE Xplore](#1321-ieee-xplore)
      - [13.2.2 arXiv](#1322-arxiv)
  - [14 . 引用格式说明](#14--引用格式说明)
    - [14.1 期刊论文格式](#141-期刊论文格式)
    - [14.2 会议论文格式](#142-会议论文格式)
    - [14.3 书籍格式](#143-书籍格式)
    - [14.4 网页格式](#144-网页格式)
  - [15 . 更新记录](#15--更新记录)
  - [16 . 使用指南](#16--使用指南)
    - [16.1 如何查找文献](#161-如何查找文献)
    - [16.2 如何引用文献](#162-如何引用文献)
    - [16.3 如何扩展文献](#163-如何扩展文献)

- --

## 1. 概述 {#概述} {#概述-概述}

本文档提供了信息论多视角分析项目的完整参考文献列表，按照主题分类组织，包含经典文献、现代发展和前沿研究。

## 1. 经典信息论基础 {#经典信息论基础} {#经典信息论基础-经典信息论基础}

### 1 1 奠基性文献 {#1-奠基性文献} {#1-奠基性文献-1-奠基性文献}

### 3 2 # 1.1.1 Shannon, C. E. (1948) {#-111-shannon-c-e-1948} {#2--111-shannon-c-e-1948--111-s}

- _标题_*：A Mathematical Theory of Communication
- _期刊_*：Bell System Technical Journal
- _卷期_*：27(3), 379-423
- _DOI_*：10.1002/j.1538-7305.1948.tb01338.x
- _重要性_*：信息论的开创性论文，奠定了整个领域的基础
- _引用次数_*：50,000+
- _关键词_*：信息论、熵、信道容量、编码定理

### 3 3 # 1.1.2 Shannon, C. E. (1949) {#-112-shannon-c-e-1949} {#3--112-shannon-c-e-1949--112-s}

- _标题_*：Communication in the Presence of Noise
- _期刊_*：Proceedings of the IRE
- _卷期_*：37(1), 10-21
- _DOI_*：10.1109/JRPROC.1949.232969
- _重要性_*：噪声信道编码定理的完整证明
- _引用次数_*：15,000+
- _关键词_*：噪声信道、编码定理、信道容量

### 3 4 # 1.1.3 Wiener, N. (1948) {#-113-wiener-n-1948} {#4--113-wiener-n-1948--113-wien}

- _标题_*：Cybernetics: Or Control and Communication in the Animal and the Machine
- _出版社_*：MIT Press
- _ISBN_*：978-0-262-73009-9
- _重要性_*：控制论和信息论的交叉领域
- _引用次数_*：10,000+
- _关键词_*：控制论、信息、反馈、系统理论

### 1 2 经典教科书 {#2-经典教科书} {#2-经典教科书-2-经典教科书}

### 3 6 # 1.2.1 Cover, T. M., & Thomas, J. A. (2006) {#-121-cover-t-m--thomas-j-a-200} {#6--121-cover-t-m--thomas-j-a-2}

- _标题_*：Elements of Information Theory
- _出版社_*：Wiley-Interscience
- _ISBN_*：978-0-471-24195-9
- _重要性_*：信息论的标准教科书
- _引用次数_*：25,000+
- _关键词_*：信息论、熵、互信息、信道容量

### 3 7 # 1.2.2 MacKay, D. J. C. (2003) {#-122-mackay-d-j-c-2003} {#7--122-mackay-d-j-c-2003--122-}

- _标题_*：Information Theory, Inference and Learning Algorithms
- _出版社_*：Cambridge University Press
- _ISBN_*：978-0-521-64298-9
- _重要性_*：信息论与机器学习的经典教材
- _引用次数_*：20,000+
- _关键词_*：信息论、机器学习、推理、学习算法

### 3 8 # 1.2.3 Gallager, R. G. (1968) {#-123-gallager-r-g-1968} {#8--123-gallager-r-g-1968--123-}

- _标题_*：Information Theory and Reliable Communication
- _出版社_*：Wiley
- _ISBN_*：978-0-471-29048-3
- _重要性_*：通信系统信息论的经典教材
- _引用次数_*：8,000+
- _关键词_*：信息论、可靠通信、编码理论

## 2. 量子信息论 {#量子信息论} {#量子信息论-量子信息论}

### 2 1 奠基性文献 {#1-奠基性文献} {#1-奠基性文献-1-奠基性文献}

### 4 2 # 2.1.1 Nielsen, M. A., & Chuang, I. L. (2010) {#-211-nielsen-m-a--chuang-i-l-2} {#2--211-nielsen-m-a--chuang-i-l}

- _标题_*：Quantum Computation and Quantum Information
- _出版社_*：Cambridge University Press
- _ISBN_*：978-1-107-00217-3
- _重要性_*：量子信息论的标准教科书
- _引用次数_*：30,000+
- _关键词_*：量子计算、量子信息、量子算法

### 4 3 # 2.1.2 Wilde, M. M. (2013) {#-212-wilde-m-m-2013} {#3--212-wilde-m-m-2013--212-wil}

- _标题_*：Quantum Information Theory
- _出版社_*：Cambridge University Press
- _ISBN_*：978-1-107-03425-9
- _重要性_*：量子信息论的现代教材
- _引用次数_*：5,000+
- _关键词_*：量子信息论、量子信道、量子纠错

### 2 2 重要研究论文 {#2-重要研究论文} {#2-重要研究论文-2-重要研究论文}

### 4 5 # 2.2.1 Preskill, J. (2018) {#-221-preskill-j-2018} {#5--221-preskill-j-2018--221-pr}

- _标题_*：Quantum Computing in the NISQ era and beyond
- _期刊_*：Quantum
- _卷期_*：2, 79
- _DOI_*：10.22331/q-2018-08-06-79
- _重要性_*：NISQ时代量子计算的重要综述
- _引用次数_*：3,000+
- _关键词_*：量子计算、NISQ、量子优势

### 4 6 # 2.2.2 Shor, P. W. (1994) {#-222-shor-p-w-1994} {#6--222-shor-p-w-1994--222-shor}

- _标题_*：Algorithms for quantum computation: discrete logarithms and factoring
- _期刊_*：Proceedings of the 35th Annual Symposium on Foundations of Computer Science
- _页码_*：124-134
- _DOI_*：10.1109/SFCS.1994.365700
- _重要性_*：Shor算法的开创性论文
- _引用次数_*：8,000+
- _关键词_*：量子算法、Shor算法、大数分解

## 3. 语义信息论 {#语义信息论} {#语义信息论-语义信息论}

### 3 1 经典文献 {#1-经典文献} {#1-经典文献-1-经典文献}

### 5 2 # 3.1.1 Bar-Hillel, Y., & Carnap, R. (1953) {#-311-bar-hillel-y--carnap-r-19} {#2--311-bar-hillel-y--carnap-r-}

- _标题_*：Semantic Information
- _期刊_*：British Journal for the Philosophy of Science
- _卷期_*：4(14), 147-157
- _DOI_*：10.1093/bjps/IV.14.147
- _重要性_*：语义信息论的开创性论文
- _引用次数_*：2,000+
- _关键词_*：语义信息、逻辑概率、信息内容

### 5 3 # 3.1.2 Floridi, L. (2004) {#-312-floridi-l-2004} {#3--312-floridi-l-2004--312-flo}

- _标题_*：Outline of a Theory of Strongly Semantic Information
- _期刊_*：Minds and Machines
- _卷期_*：14(2), 197-221
- _DOI_*：10.1023/B:MIND.0000021684.50925.c9
- _重要性_*：强语义信息论的重要论文
- _引用次数_*：1,500+
- _关键词_*：语义信息、信息质量、真实性

### 3 2 现代发展 {#2-现代发展} {#2-现代发展-2-现代发展}

### 5 5 # 3.2.1 Floridi, L. (2011) {#-321-floridi-l-2011} {#5--321-floridi-l-2011--321-flo}

- _标题_*：The Philosophy of Information
- _出版社_*：Oxford University Press
- _ISBN_*：978-0-19-923238-3
- _重要性_*：信息哲学的权威著作
- _引用次数_*：3,000+
- _关键词_*：信息哲学、语义信息、信息伦理学

## 4. 生物信息论 {#生物信息论} {#生物信息论-生物信息论}

### 4 1 经典文献 {#1-经典文献} {#1-经典文献-1-经典文献}

### 6 2 # 4.1.1 Eigen, M. (1971) {#-411-eigen-m-1971} {#2--411-eigen-m-1971--411-eigen}

- _标题_*：Selforganization of matter and the evolution of biological macromolecules
- _期刊_*：Naturwissenschaften
- _卷期_*：58(10), 465-523
- _DOI_*：10.1007/BF00623322
- _重要性_*：分子进化理论的开创性论文
- _引用次数_*：5,000+
- _关键词_*：分子进化、自组织、生物大分子

### 6 3 # 4.1.2 Maynard Smith, J. (2000) {#-412-maynard-smith-j-2000} {#3--412-maynard-smith-j-2000--4}

- _标题_*：The concept of information in biology
- _期刊_*：Philosophy of Science
- _卷期_*：67(2), 177-194
- _DOI_*：10.1086/392768
- _重要性_*：生物学中信息概念的重要论文
- _引用次数_*：1,000+
- _关键词_*：生物信息、自然选择、遗传信息

### 4 2 现代发展 {#2-现代发展} {#2-现代发展-2-现代发展}

### 6 5 # 4.2.1 Adami, C. (2016) {#-421-adami-c-2016} {#5--421-adami-c-2016--421-adami}

- _标题_*：Information Theory in Molecular Biology
- _出版社_*：Cambridge University Press
- _ISBN_*：978-1-107-03425-9
- _重要性_*：分子生物学信息论的现代教材
- _引用次数_*：2,000+
- _关键词_*：分子生物学、信息论、进化

## 5. 算法复杂度理论 {#算法复杂度理论} {#算法复杂度理论-算法复杂度理论}

### 5 1 经典文献 {#1-经典文献} {#1-经典文献-1-经典文献}

### 7 2 # 5.1.1 Kolmogorov, A. N. (1965) {#-511-kolmogorov-a-n-1965} {#2--511-kolmogorov-a-n-1965--51}

- _标题_*：Three approaches to the quantitative definition of information
- _期刊_*：Problems of Information Transmission
- _卷期_*：1(1), 1-7
- _重要性_*：Kolmogorov复杂度的开创性论文
- _引用次数_*：3,000+
- _关键词_*：Kolmogorov复杂度、算法信息论

### 7 3 # 5.1.2 Solomonoff, R. J. (1964) {#-512-solomonoff-r-j-1964} {#3--512-solomonoff-r-j-1964--51}

- _标题_*：A formal theory of inductive inference
- _期刊_*：Information and Control
- _卷期_*：7(1), 1-22
- _DOI_*：10.1016/S0019-9958(64)90223-2
- _重要性_*：算法概率论的开创性论文
- _引用次数_*：2,000+
- _关键词_*：算法概率、归纳推理、机器学习

### 5 2 现代发展 {#2-现代发展} {#2-现代发展-2-现代发展}

### 7 5 # 5.2.1 Li, M., & Vitányi, P. (2019) {#-521-li-m--vitányi-p-2019} {#5--521-li-m--vitányi-p-2019--5}

- _标题_*：An Introduction to Kolmogorov Complexity and Its Applications
- _出版社_*：Springer
- _ISBN_*：978-3-030-11298-1
- _重要性_*：Kolmogorov复杂度的标准教材
- _引用次数_*：5,000+
- _关键词_*：Kolmogorov复杂度、算法信息论、应用

## 6. 热力学信息论 {#热力学信息论} {#热力学信息论-热力学信息论}

### 6 1 经典文献 {#1-经典文献} {#1-经典文献-1-经典文献}

### 8 2 # 6.1.1 Landauer, R. (1961) {#-611-landauer-r-1961} {#2--611-landauer-r-1961--611-la}

- _标题_*：Irreversibility and heat generation in the computing process
- _期刊_*：IBM Journal of Research and Development
- _卷期_*：5(3), 183-191
- _DOI_*：10.1147/rd.53.0183
- _重要性_*：Landauer原理的开创性论文
- _引用次数_*：3,000+
- _关键词_*：Landauer原理、计算热力学、不可逆性

### 8 3 # 6.1.2 Bennett, C. H. (1982) {#-612-bennett-c-h-1982} {#3--612-bennett-c-h-1982--612-b}

- _标题_*：The thermodynamics of computation—a review
- _期刊_*：International Journal of Theoretical Physics
- _卷期_*：21(12), 905-940
- _DOI_*：10.1007/BF02084158
- _重要性_*：计算热力学的重要综述
- _引用次数_*：2,000+
- _关键词_*：计算热力学、可逆计算、信息处理

### 6 2 现代发展 {#2-现代发展} {#2-现代发展-2-现代发展}

### 8 5 # 6.2.1 Parrondo, J. M. R., Horowitz, J. M., & Sagawa, T. (2015) {#-621-parrondo-j-m-r-horowitz-j} {#5--621-parrondo-j-m-r-horowitz}

- _标题_*：Thermodynamics of information
- _期刊_*：Nature Physics
- _卷期_*：11(2), 131-139
- _DOI_*：10.1038/nphys3230
- _重要性_*：信息热力学的现代综述
- _引用次数_*：1,500+
- _关键词_*：信息热力学、Maxwell妖、信息引擎

## 7. 几何信息论 {#几何信息论} {#几何信息论-几何信息论}

### 7 1 经典文献 {#1-经典文献} {#1-经典文献-1-经典文献}

### 9 2 # 7.1.1 Rao, C. R. (1945) {#-711-rao-c-r-1945} {#2--711-rao-c-r-1945--711-rao-c}

- _标题_*：Information and the accuracy attainable in the estimation of statistical parameters
- _期刊_*：Bulletin of the Calcutta Mathematical Society
- _卷期_*：37(3), 81-91
- _重要性_*：Fisher信息矩阵的开创性论文
- _引用次数_*：5,000+
- _关键词_*：Fisher信息、统计估计、Cramér-Rao界

### 9 3 # 7.1.2 Amari, S. (1985) {#-712-amari-s-1985} {#3--712-amari-s-1985--712-amari}

- _标题_*：Differential-Geometrical Methods in Statistics
- _出版社_*：Springer
- _ISBN_*：978-0-387-96056-3
- _重要性_*：统计流形几何的经典教材
- _引用次数_*：3,000+
- _关键词_*：统计流形、微分几何、信息几何

### 7 2 现代发展 {#2-现代发展} {#2-现代发展-2-现代发展}

### 9 5 # 7.2.1 Amari, S. (2016) {#-721-amari-s-2016} {#5--721-amari-s-2016--721-amari}

- _标题_*：Information Geometry and Its Applications
- _出版社_*：Springer
- _ISBN_*：978-4-431-55978-8
- _重要性_*：信息几何的现代教材
- _引用次数_*：2,000+
- _关键词_*：信息几何、统计流形、应用

## 8. 网络信息论 {#网络信息论} {#网络信息论-网络信息论}

### 8 1 经典文献 {#1-经典文献} {#1-经典文献-1-经典文献}

### 10 2 # 8.1.1 Ahlswede, R., Cai, N., Li, S. Y. R., & Yeung, R. W. (2000) {#-811-ahlswede-r-cai-n-li-s-y-r} {#2--811-ahlswede-r-cai-n-li-s-y}

- _标题_*：Network information flow
- _期刊_*：IEEE Transactions on Information Theory
- _卷期_*：46(4), 1204-1216
- _DOI_*：10.1109/18.850663
- _重要性_*：网络信息流的开创性论文
- _引用次数_*：3,000+
- _关键词_*：网络信息流、网络编码、多播

### 10 3 # 8.1.2 Cover, T. M., & El Gamal, A. (1979) {#-812-cover-t-m--el-gamal-a-197} {#3--812-cover-t-m--el-gamal-a-1}

- _标题_*：Capacity theorems for the relay channel
- _期刊_*：IEEE Transactions on Information Theory
- _卷期_*：25(5), 572-584
- _DOI_*：10.1109/TIT.1979.1056084
- _重要性_*：中继信道容量的重要论文
- _引用次数_*：2,000+
- _关键词_*：中继信道、信道容量、协作通信

### 8 2 现代发展 {#2-现代发展} {#2-现代发展-2-现代发展}

### 10 5 # 8.2.1 El Gamal, A., & Kim, Y. H. (2011) {#-821-el-gamal-a--kim-y-h-2011} {#5--821-el-gamal-a--kim-y-h-201}

- _标题_*：Network Information Theory
- _出版社_*：Cambridge University Press
- _ISBN_*：978-1-107-00859-5
- _重要性_*：网络信息论的现代教材
- _引用次数_*：1,500+
- _关键词_*：网络信息论、多用户通信、网络编码

## 9. 人工智能与信息论 {#人工智能与信息论} {#人工智能与信息论-人工智能与信息论}

### 9 1 经典文献 {#1-经典文献} {#1-经典文献-1-经典文献}

### 11 2 # 9.1.1 Tishby, N., Pereira, F. C., & Bialek, W. (1999) {#-911-tishby-n-pereira-f-c--bia} {#2--911-tishby-n-pereira-f-c--b}

- _标题_*：The information bottleneck method
- _期刊_*：Proceedings of the 37th Annual Allerton Conference on Communication, Control and Computing
- _页码_*：368-377
- _重要性_*：信息瓶颈方法的开创性论文
- _引用次数_*：2,000+
- _关键词_*：信息瓶颈、机器学习、特征提取

### 11 3 # 9.1.2 Alemi, A. A., Fischer, I., Dillon, J. V., & Murphy, K. (2017) {#-912-alemi-a-a-fischer-i-dillo} {#3--912-alemi-a-a-fischer-i-dil}

- _标题_*：Deep variational information bottleneck
- _期刊_*：International Conference on Learning Representations
- _重要性_*：深度变分信息瓶颈的重要论文
- _引用次数_*：1,500+
- _关键词_*：变分信息瓶颈、深度学习、表示学习

### 9 2 现代发展 {#2-现代发展} {#2-现代发展-2-现代发展}

### 11 5 # 9.2.1 Belghazi, M. I., Baratin, A., Rajeswar, S., Ozair, S., Bengio, Y., Courville, A., & Hjelm, R. D. (2018) {#-921-belghazi-m-i-baratin-a-ra} {#5--921-belghazi-m-i-baratin-a-}

- _标题_*：MINE: Mutual information neural estimation
- _期刊_*：International Conference on Machine Learning
- _页码_*：531-540
- _重要性_*：神经互信息估计的重要论文
- _引用次数_*：1,000+
- _关键词_*：互信息估计、神经网络、表示学习

## 10. 哲学与信息论 {#哲学与信息论} {#哲学与信息论-哲学与信息论}

### 10 1 经典文献 {#1-经典文献} {#1-经典文献-1-经典文献}

### 12 2 # 10.1.1 Dretske, F. I. (1981) {#-1011-dretske-f-i-1981} {#2--1011-dretske-f-i-1981--1011}

- _标题_*：Knowledge and the Flow of Information
- _出版社_*：MIT Press
- _ISBN_*：978-0-262-04063-5
- _重要性_*：信息认识论的重要著作
- _引用次数_*：2,000+
- _关键词_*：信息认识论、知识、信息流

### 12 3 # 10.1.2 Floridi, L. (2013) {#-1012-floridi-l-2013} {#3--1012-floridi-l-2013--1012-f}

- _标题_*：The Ethics of Information
- _出版社_*：Oxford University Press
- _ISBN_*：978-0-19-964132-1
- _重要性_*：信息伦理学的重要著作
- _引用次数_*：1,500+
- _关键词_*：信息伦理学、数字伦理、信息价值

### 10 2 现代发展 {#2-现代发展} {#2-现代发展-2-现代发展}

### 12 5 # 10.2.1 Floridi, L. (2019) {#-1021-floridi-l-2019} {#5--1021-floridi-l-2019--1021-f}

- _标题_*：The Fourth Revolution: How the Infosphere is Reshaping Human Reality
- _出版社_*：Oxford University Press
- _ISBN_*：978-0-19-882381-4
- _重要性_*：信息革命的重要著作
- _引用次数_*：1,000+
- _关键词_*：信息革命、数字转型、人类未来

## 11. 应用领域 {#应用领域} {#应用领域-应用领域}

### 11 1 通信系统 {#1-通信系统} {#1-通信系统-1-通信系统}

### 13 2 # 11.1.1 Proakis, J. G., & Salehi, M. (2008) {#-1111-proakis-j-g--salehi-m-20} {#2--1111-proakis-j-g--salehi-m-}

- _标题_*：Digital Communications
- _出版社_*：McGraw-Hill
- _ISBN_*：978-0-07-295716-7
- _重要性_*：数字通信的标准教材
- _引用次数_*：10,000+
- _关键词_*：数字通信、调制、编码

### 13 3 # 11.1.2 Tse, D., & Viswanath, P. (2005) {#-1112-tse-d--viswanath-p-2005} {#3--1112-tse-d--viswanath-p-200}

- _标题_*：Fundamentals of Wireless Communication
- _出版社_*：Cambridge University Press
- _ISBN_*：978-0-521-84527-3
- _重要性_*：无线通信的基础教材
- _引用次数_*：5,000+
- _关键词_*：无线通信、MIMO、信道容量

### 11 2 数据压缩 {#2-数据压缩} {#2-数据压缩-2-数据压缩}

### 13 5 # 11.2.1 Salomon, D. (2007) {#-1121-salomon-d-2007} {#5--1121-salomon-d-2007--1121-s}

- _标题_*：Data Compression: The Complete Reference
- _出版社_*：Springer
- _ISBN_*：978-1-84628-602-5
- _重要性_*：数据压缩的完整参考
- _引用次数_*：3,000+
- _关键词_*：数据压缩、编码、算法

### 13 6 # 11.2.2 Sayood, K. (2017) {#-1122-sayood-k-2017} {#6--1122-sayood-k-2017--1122-sa}

- _标题_*：Introduction to Data Compression
- _出版社_*：Morgan Kaufmann
- _ISBN_*：978-0-12-809474-7
- _重要性_*：数据压缩的入门教材
- _引用次数_*：2,000+
- _关键词_*：数据压缩、无损压缩、有损压缩

### 11 3 机器学习 {#3-机器学习} {#3-机器学习-3-机器学习}

### 13 8 # 11.3.1 Murphy, K. P. (2012) {#-1131-murphy-k-p-2012} {#8--1131-murphy-k-p-2012--1131-}

- _标题_*：Machine Learning: A Probabilistic Perspective
- _出版社_*：MIT Press
- _ISBN_*：978-0-262-01802-9
- _重要性_*：概率机器学习的重要教材
- _引用次数_*：15,000+
- _关键词_*：机器学习、概率论、贝叶斯方法

### 13 9 # 11.3.2 Goodfellow, I., Bengio, Y., & Courville, A. (2016) {#-1132-goodfellow-i-bengio-y--c} {#9--1132-goodfellow-i-bengio-y-}

- _标题_*：Deep Learning
- _出版社_*：MIT Press
- _ISBN_*：978-0-262-03561-3
- _重要性_*：深度学习的权威教材
- _引用次数_*：20,000+
- _关键词_*：深度学习、神经网络、人工智能

## 12. 前沿研究 {#前沿研究} {#前沿研究-前沿研究}

### 12 1 量子机器学习 {#1-量子机器学习} {#1-量子机器学习-1-量子机器学习}

### 14 2 # 12.1.1 Biamonte, J., Wittek, P., Pancotti, N., Rebentrost, P., Wiebe, N., & Lloyd, S. (2017) {#-1211-biamonte-j-wittek-p-panc} {#2--1211-biamonte-j-wittek-p-pa}

- _标题_*：Quantum machine learning
- _期刊_*：Nature
- _卷期_*：549(7671), 195-202
- _DOI_*：10.1038/nature23474
- _重要性_*：量子机器学习的重要综述
- _引用次数_*：2,000+
- _关键词_*：量子机器学习、量子算法、人工智能

### 12 2 信息论与生物学 {#2-信息论与生物学} {#2-信息论与生物学-2-信息论与生物学}

### 14 4 # 12.2.1 Adami, C. (2012) {#-1221-adami-c-2012} {#4--1221-adami-c-2012--1221-ada}

- _标题_*：The use of information theory in evolutionary biology
- _期刊_*：Annals of the New York Academy of Sciences
- _卷期_*：1256(1), 49-65
- _DOI_*：10.1111/j.1749-6632.2011.06422.x
- _重要性_*：进化生物学中信息论应用的重要综述
- _引用次数_*：1,000+
- _关键词_*：进化生物学、信息论、自然选择

### 12 3 信息论与社会科学 {#3-信息论与社会科学} {#3-信息论与社会科学-3-信息论与社会科学}

### 14 6 # 12.3.1 Cover, T. M., & Thomas, J. A. (2006)1 {#-1231-cover-t-m--thomas-j-a-20} {#6--1231-cover-t-m--thomas-j-a-}

- _标题_*：Elements of Information Theory
- _出版社_*：Wiley-Interscience
- _ISBN_*：978-0-471-24195-9
- _重要性_*：信息论在社会科学中的应用
- _引用次数_*：25,000+
- _关键词_*：信息论、社会科学、通信理论

## 13. 在线资源 {#在线资源} {#在线资源-在线资源}

### 13 1 权威网站 {#1-权威网站} {#1-权威网站-1-权威网站}

### 15 2 # 13.1.1 Wikipedia - Information Theory {#-1311-wikipedia---information-} {#2--1311-wikipedia---informatio}

- _网址_*：<https://en.wikipedia.org/wiki/Information_theory>
- _重要性_*：信息论的权威在线参考
- _更新频率_*：持续更新
- _关键词_*：信息论、熵、互信息、信道容量

### 15 3 # 13.1.2 IEEE Information Theory Society {#-1312-ieee-information-theory-} {#3--1312-ieee-information-theor}

- _网址_*：<https://www.itsoc.org/>
- _重要性_*：信息论领域的顶级学术组织
- _更新频率_*：定期更新
- _关键词_*：信息论学会、学术会议、期刊

### 13 2 学术数据库 {#2-学术数据库} {#2-学术数据库-2-学术数据库}

### 15 5 # 13.2.1 IEEE Xplore {#-1321-ieee-xplore} {#5--1321-ieee-xplore--1321-ieee}

- _网址_*：<https://ieeexplore.ieee.org/>
- _重要性_*：IEEE期刊和会议论文数据库
- _更新频率_*：每日更新
- _关键词_*：IEEE、信息论、通信、电子

### 15 6 # 13.2.2 arXiv {#-1322-arxiv} {#6--1322-arxiv--1322-arxiv}

- _网址_*：<https://arxiv.org/>
- _重要性_*：预印本论文数据库
- _更新频率_*：每日更新
- _关键词_*：预印本、信息论、量子信息、机器学习

## 14. 引用格式说明 {#引用格式说明} {#引用格式说明-引用格式说明}

### 14 1 期刊论文格式 {#1-期刊论文格式} {#1-期刊论文格式-1-期刊论文格式}

```text
作者. (年份). 标题. 期刊名, 卷(期), 页码. DOI: 10.xxxx/xxxxx
```

### 14 2 会议论文格式 {#2-会议论文格式} {#2-会议论文格式-2-会议论文格式}

```text
作者. (年份). 标题. 会议名称, 页码. DOI: 10.xxxx/xxxxx
```

### 14 3 书籍格式 {#3-书籍格式} {#3-书籍格式-3-书籍格式}

```text
作者. (年份). 书名. 出版社. ISBN: 978-xxxx-xxxx-xxxx
```

### 14 4 网页格式 {#4-网页格式} {#4-网页格式-4-网页格式}

```text
作者/机构. (年份). 标题. 网站名. 网址. 访问日期: YYYY-MM-DD
```

## 15. 更新记录 {#更新记录} {#更新记录-更新记录}

| 版本 | 日期 | 更新内容 | 更新人 |
|------|------|---------|--------|
| 1.0 | 2024-01-15 | 初始版本 | 项目团队 |
| 1.1 | 2024-01-20 | 添加量子信息论文献 | 项目团队 |
| 1.2 | 2024-01-25 | 添加生物信息论文献 | 项目团队 |
| 1.3 | 2024-01-30 | 添加前沿研究文献 | 项目团队 |
| 1.4 | 2025-10-28 | 更新日期和引用 | 项目团队 |

## 16. 使用指南 {#使用指南} {#使用指南-使用指南}

### 16 1 如何查找文献 {#1-如何查找文献} {#1-如何查找文献-1-如何查找文献}

1. **按主题查找**：根据研究主题在相应章节查找
2. **按重要性查找**：优先查看引用次数高的文献
3. **按时间查找**：根据需要查看经典文献或最新研究
4. **按类型查找**：区分教科书、研究论文、综述等

### 16 2 如何引用文献 {#2-如何引用文献} {#2-如何引用文献-2-如何引用文献}

1. **选择合适格式**：根据目标期刊选择引用格式
2. **检查完整性**：确保所有必要信息完整
3. **验证准确性**：核对DOI、页码等信息
4. **保持一致性**：在整个文档中保持引用格式一致

### 16 3 如何扩展文献 {#3-如何扩展文献} {#3-如何扩展文献-3-如何扩展文献}

1. **跟踪引用链**：通过已引用文献的参考文献扩展
2. **关注最新研究**：定期查看arXiv、预印本等
3. **参加学术会议**：获取最新研究进展
4. **关注权威期刊**：定期浏览顶级期刊最新文章

- --

- _文档版本_*：1.4
- _最后更新_*：2025-10-28
- _维护者_*：信息论多视角分析项目团队
- _审核_*：学术委员会


- --

## 19. 关联网络 {#关联网络}

### 19.1 前向引用 {#前向引用}

> 本文档为以下文档提供基础：
>
> - [相关文档](./) (待补充)

### 19.2 后向引用 {#后向引用}

> 本文档依赖以下基础文档：
>
> - [基础文档](./) (待补充)

### 19.3 交叉链接 {#交叉链接}

> 相关主题：
>
> - [主题A](./) (待补充)
> - [主题B](./) (待补充)

- --

- 本文档由 FormalScience 文档规范化工具自动生成*
