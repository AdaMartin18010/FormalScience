# 形式语言理论

## 目录结构

```
03_Formal_Language_Theory/
├── README.md                    # 主目录文件
├── 01_Basic_Concepts/          # 基本概念
├── 02_Regular_Languages/       # 正则语言
├── 03_Context_Free_Languages/  # 上下文无关语言
├── 04_Context_Sensitive_Languages/ # 上下文相关语言
├── 05_Recursively_Enumerable_Languages/ # 递归可枚举语言
├── 06_Automata_Theory/         # 自动机理论
├── 07_Grammar_Theory/          # 文法理论
├── 08_Computational_Complexity/ # 计算复杂性
├── 09_Formal_Semantics/        # 形式语义
├── 10_Language_Processing/     # 语言处理
└── 11_Synthesis/               # 综合理论
```

## 1. 基本概念 (01_Basic_Concepts)

### 1.1 语言基础

- [1.1.1 字母表与字符串](./01_Basic_Concepts/01_Alphabets_and_Strings.md)
- [1.1.2 语言定义](./01_Basic_Concepts/02_Language_Definition.md)
- [1.1.3 语言运算](./01_Basic_Concepts/03_Language_Operations.md)
- [1.1.4 语言关系](./01_Basic_Concepts/04_Language_Relations.md)

### 1.2 形式化基础

- [1.2.1 形式系统](./01_Basic_Concepts/05_Formal_Systems.md)
- [1.2.2 抽象语法](./01_Basic_Concepts/06_Abstract_Syntax.md)
- [1.2.3 具体语法](./01_Basic_Concepts/07_Concrete_Syntax.md)
- [1.2.4 语法树](./01_Basic_Concepts/08_Syntax_Trees.md)

## 2. 正则语言 (02_Regular_Languages)

### 2.1 正则表达式

- [2.1.1 正则表达式基础](./02_Regular_Languages/01_Regular_Expression_Basics.md)
- [2.1.2 正则表达式运算](./02_Regular_Languages/02_Regular_Expression_Operations.md)
- [2.1.3 正则表达式等价性](./02_Regular_Languages/03_Regular_Expression_Equivalence.md)
- [2.1.4 正则表达式最小化](./02_Regular_Languages/04_Regular_Expression_Minimization.md)

### 2.2 有限自动机

- [2.2.1 确定性有限自动机](./02_Regular_Languages/05_Deterministic_Finite_Automata.md)
- [2.2.2 非确定性有限自动机](./02_Regular_Languages/06_Nondeterministic_Finite_Automata.md)
- [2.2.3 自动机等价性](./02_Regular_Languages/07_Automata_Equivalence.md)
- [2.2.4 自动机最小化](./02_Regular_Languages/08_Automata_Minimization.md)

### 2.3 正则语言性质

- [2.3.1 泵引理](./02_Regular_Languages/09_Pumping_Lemma.md)
- [2.3.2 正则语言闭包性质](./02_Regular_Languages/10_Closure_Properties.md)
- [2.3.3 正则语言判定问题](./02_Regular_Languages/11_Decision_Problems.md)
- [2.3.4 正则语言应用](./02_Regular_Languages/12_Applications.md)

## 3. 上下文无关语言 (03_Context_Free_Languages)

### 3.1 上下文无关文法

- [3.1.1 上下文无关文法基础](./03_Context_Free_Languages/01_Context_Free_Grammar_Basics.md)
- [3.1.2 文法变换](./03_Context_Free_Languages/02_Grammar_Transformations.md)
- [3.1.3 乔姆斯基范式](./03_Context_Free_Languages/03_Chomsky_Normal_Form.md)
- [3.1.4 格雷巴赫范式](./03_Context_Free_Languages/04_Greibach_Normal_Form.md)

### 3.2 下推自动机

- [3.2.1 下推自动机基础](./03_Context_Free_Languages/05_Pushdown_Automata_Basics.md)
- [3.2.2 确定性下推自动机](./03_Context_Free_Languages/06_Deterministic_Pushdown_Automata.md)
- [3.2.3 自动机与文法等价性](./03_Context_Free_Languages/07_Automata_Grammar_Equivalence.md)
- [3.2.4 下推自动机应用](./03_Context_Free_Languages/08_Pushdown_Automata_Applications.md)

### 3.3 上下文无关语言性质

- [3.3.1 泵引理](./03_Context_Free_Languages/09_Pumping_Lemma.md)
- [3.3.2 闭包性质](./03_Context_Free_Languages/10_Closure_Properties.md)
- [3.3.3 判定问题](./03_Context_Free_Languages/11_Decision_Problems.md)
- [3.3.4 歧义性](./03_Context_Free_Languages/12_Ambiguity.md)

## 4. 上下文相关语言 (04_Context_Sensitive_Languages)

### 4.1 上下文相关文法

- [4.1.1 上下文相关文法基础](./04_Context_Sensitive_Languages/01_Context_Sensitive_Grammar_Basics.md)
- [4.1.2 文法形式](./04_Context_Sensitive_Languages/02_Grammar_Forms.md)
- [4.1.3 文法变换](./04_Context_Sensitive_Languages/03_Grammar_Transformations.md)
- [4.1.4 文法应用](./04_Context_Sensitive_Languages/04_Grammar_Applications.md)

### 4.2 线性有界自动机

- [4.2.1 线性有界自动机基础](./04_Context_Sensitive_Languages/05_Linear_Bounded_Automata_Basics.md)
- [4.2.2 自动机与文法等价性](./04_Context_Sensitive_Languages/06_Automata_Grammar_Equivalence.md)
- [4.2.3 自动机应用](./04_Context_Sensitive_Languages/07_Automata_Applications.md)

### 4.3 上下文相关语言性质

- [4.3.1 语言性质](./04_Context_Sensitive_Languages/08_Language_Properties.md)
- [4.3.2 闭包性质](./04_Context_Sensitive_Languages/09_Closure_Properties.md)
- [4.3.3 判定问题](./04_Context_Sensitive_Languages/10_Decision_Problems.md)

## 5. 递归可枚举语言 (05_Recursively_Enumerable_Languages)

### 5.1 无限制文法

- [5.1.1 无限制文法基础](./05_Recursively_Enumerable_Languages/01_Unrestricted_Grammar_Basics.md)
- [5.1.2 文法形式](./05_Recursively_Enumerable_Languages/02_Grammar_Forms.md)
- [5.1.3 文法应用](./05_Recursively_Enumerable_Languages/03_Grammar_Applications.md)

### 5.2 图灵机

- [5.2.1 图灵机基础](./05_Recursively_Enumerable_Languages/04_Turing_Machine_Basics.md)
- [5.2.2 图灵机变种](./05_Recursively_Enumerable_Languages/05_Turing_Machine_Variants.md)
- [5.2.3 图灵机与文法等价性](./05_Recursively_Enumerable_Languages/06_Turing_Machine_Grammar_Equivalence.md)
- [5.2.4 图灵机应用](./05_Recursively_Enumerable_Languages/07_Turing_Machine_Applications.md)

### 5.3 递归可枚举语言性质

- [5.3.1 语言性质](./05_Recursively_Enumerable_Languages/08_Language_Properties.md)
- [5.3.2 闭包性质](./05_Recursively_Enumerable_Languages/09_Closure_Properties.md)
- [5.3.3 判定问题](./05_Recursively_Enumerable_Languages/10_Decision_Problems.md)

## 6. 自动机理论 (06_Automata_Theory)

### 6.1 自动机基础

- [6.1.1 自动机基本概念](./06_Automata_Theory/01_Automata_Basic_Concepts.md)
- [6.1.2 自动机分类](./06_Automata_Theory/02_Automata_Classification.md)
- [6.1.3 自动机等价性](./06_Automata_Theory/03_Automata_Equivalence.md)
- [6.1.4 自动机最小化](./06_Automata_Theory/04_Automata_Minimization.md)

### 6.2 高级自动机

- [6.2.1 双向自动机](./06_Automata_Theory/05_Two_Way_Automata.md)
- [6.2.2 概率自动机](./06_Automata_Theory/06_Probabilistic_Automata.md)
- [6.2.3 量子自动机](./06_Automata_Theory/07_Quantum_Automata.md)
- [6.2.4 细胞自动机](./06_Automata_Theory/08_Cellular_Automata.md)

### 6.3 自动机应用

- [6.3.1 编译器设计](./06_Automata_Theory/09_Compiler_Design.md)
- [6.3.2 模式识别](./06_Automata_Theory/10_Pattern_Recognition.md)
- [6.3.3 自然语言处理](./06_Automata_Theory/11_Natural_Language_Processing.md)
- [6.3.4 生物信息学](./06_Automata_Theory/12_Bioinformatics.md)

## 7. 文法理论 (07_Grammar_Theory)

### 7.1 文法基础

- [7.1.1 文法基本概念](./07_Grammar_Theory/01_Grammar_Basic_Concepts.md)
- [7.1.2 文法分类](./07_Grammar_Theory/02_Grammar_Classification.md)
- [7.1.3 文法等价性](./07_Grammar_Theory/03_Grammar_Equivalence.md)
- [7.1.4 文法变换](./07_Grammar_Theory/04_Grammar_Transformations.md)

### 7.2 高级文法

- [7.2.1 属性文法](./07_Grammar_Theory/05_Attribute_Grammars.md)
- [7.2.2 树邻接文法](./07_Grammar_Theory/06_Tree_Adjoining_Grammars.md)
- [7.2.3 范畴文法](./07_Grammar_Theory/07_Categorial_Grammars.md)
- [7.2.4 依存文法](./07_Grammar_Theory/08_Dependency_Grammars.md)

### 7.3 文法应用

- [7.3.1 语法分析](./07_Grammar_Theory/09_Syntax_Analysis.md)
- [7.3.2 语义分析](./07_Grammar_Theory/10_Semantic_Analysis.md)
- [7.3.3 代码生成](./07_Grammar_Theory/11_Code_Generation.md)
- [7.3.4 自然语言处理](./07_Grammar_Theory/12_Natural_Language_Processing.md)

## 8. 计算复杂性 (08_Computational_Complexity)

### 8.1 语言复杂性

- [8.1.1 时间复杂性](./08_Computational_Complexity/01_Time_Complexity.md)
- [8.1.2 空间复杂性](./08_Computational_Complexity/02_Space_Complexity.md)
- [8.1.3 复杂性类](./08_Computational_Complexity/03_Complexity_Classes.md)
- [8.1.4 复杂性关系](./08_Computational_Complexity/04_Complexity_Relations.md)

### 8.2 算法复杂性

- [8.2.1 解析算法](./08_Computational_Complexity/05_Parsing_Algorithms.md)
- [8.2.2 识别算法](./08_Computational_Complexity/06_Recognition_Algorithms.md)
- [8.2.3 最小化算法](./08_Computational_Complexity/07_Minimization_Algorithms.md)
- [8.2.4 优化算法](./08_Computational_Complexity/08_Optimization_Algorithms.md)

## 9. 形式语义 (09_Formal_Semantics)

### 9.1 语义基础

- [9.1.1 语义基本概念](./09_Formal_Semantics/01_Semantics_Basic_Concepts.md)
- [9.1.2 指称语义](./09_Formal_Semantics/02_Denotational_Semantics.md)
- [9.1.3 操作语义](./09_Formal_Semantics/03_Operational_Semantics.md)
- [9.1.4 公理语义](./09_Formal_Semantics/04_Axiomatic_Semantics.md)

### 9.2 高级语义

- [9.2.1 类型语义](./09_Formal_Semantics/05_Type_Semantics.md)
- [9.2.2 逻辑语义](./09_Formal_Semantics/06_Logical_Semantics.md)
- [9.2.3 代数语义](./09_Formal_Semantics/07_Algebraic_Semantics.md)
- [9.2.4 范畴语义](./09_Formal_Semantics/08_Categorical_Semantics.md)

## 10. 语言处理 (10_Language_Processing)

### 10.1 语法处理

- [10.1.1 词法分析](./10_Language_Processing/01_Lexical_Analysis.md)
- [10.1.2 语法分析](./10_Language_Processing/02_Syntax_Analysis.md)
- [10.1.3 语义分析](./10_Language_Processing/03_Semantic_Analysis.md)
- [10.1.4 代码生成](./10_Language_Processing/04_Code_Generation.md)

### 10.2 语言应用

- [10.2.1 编译器设计](./10_Language_Processing/05_Compiler_Design.md)
- [10.2.2 解释器设计](./10_Language_Processing/06_Interpreter_Design.md)
- [10.2.3 自然语言处理](./10_Language_Processing/07_Natural_Language_Processing.md)
- [10.2.4 形式验证](./10_Language_Processing/08_Formal_Verification.md)

## 11. 综合理论 (11_Synthesis)

### 11.1 理论综合

- [11.1.1 语言理论统一](./11_Synthesis/01_Language_Theory_Unification.md)
- [11.1.2 自动机理论综合](./11_Synthesis/02_Automata_Theory_Synthesis.md)
- [11.1.3 文法理论综合](./11_Synthesis/03_Grammar_Theory_Synthesis.md)
- [11.1.4 语义理论综合](./11_Synthesis/04_Semantics_Theory_Synthesis.md)

### 11.2 应用综合

- [11.2.1 编程语言设计](./11_Synthesis/05_Programming_Language_Design.md)
- [11.2.2 形式化方法](./11_Synthesis/06_Formal_Methods.md)
- [11.2.3 人工智能应用](./11_Synthesis/07_Artificial_Intelligence_Applications.md)
- [11.2.4 系统理论应用](./11_Synthesis/08_Systems_Theory_Applications.md)

## 导航链接

- [返回主索引](../00_Master_Index/README.md)
- [哲学基础理论](../01_Philosophical_Foundation/README.md)
- [数学基础理论](../02_Mathematical_Foundation/README.md)

## 构建状态

- [x] 目录结构建立
- [ ] 基本概念内容
- [ ] 正则语言内容
- [ ] 上下文无关语言内容
- [ ] 上下文相关语言内容
- [ ] 递归可枚举语言内容
- [ ] 自动机理论内容
- [ ] 文法理论内容
- [ ] 计算复杂性内容
- [ ] 形式语义内容
- [ ] 语言处理内容
- [ ] 综合理论内容

## 更新日志

- 2024-12-20: 创建形式语言理论目录结构
- 2024-12-20: 建立完整的树形导航体系
