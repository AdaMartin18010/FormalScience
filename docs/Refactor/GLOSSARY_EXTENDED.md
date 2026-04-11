# 扩展术语表 (Extended Glossary)

> 本文档提供FormalScience项目中使用的数学、计算机科学和形式化验证领域术语的详细解释。

---

## 📖 使用说明

- **术语格式**: 英文术语 (中文翻译)
- **详细解释**: 提供概念定义和应用场景
- **相关概念**: 链接到相关术语

---

## A

### Abstract Algebra (抽象代数)

研究代数结构（如群、环、域）的数学分支，关注结构及其同态映射的性质。
> **相关**: [Group](#group-群), [Ring](#ring-环), [Field](#field-域)

### Abstraction (抽象)

提取共同特征、忽略具体细节的过程。在形式化验证中，通过抽象简化复杂系统分析。

### Additive Notation (加法记号)

群的二元运算使用加号(+)表示，常见于阿贝尔群。与乘法记号相对。
> **相关**: [Multiplicative Notation](#multiplicative-notation-乘法记号)

### Agda

一种依赖类型函数式编程语言，也用作定理证明器。
> **相关**: [Coq](#coq), [Lean](#lean)

### Algebraic Data Type (ADT, 代数数据类型)

通过积类型和和类型组合构造的数据类型。

```lean
inductive Tree (α : Type)
  | leaf : Tree α           -- 和类型的构造子
  | node : α → Tree α → Tree α → Tree α
```

### Algorithm (算法)

解决特定问题的一系列明确、有限的计算步骤。

### Antisymmetric (反对称)

关系R满足：若aRb且bRa，则a = b。

### Application (应用/函数应用)

将函数应用于参数，记作 `f x`。

### Associativity (结合律)

运算满足 `(a ∘ b) ∘ c = a ∘ (b ∘ c)`。
> **相关**: [Commutativity](#commutativity-交换律)

### Assumption (假设)

证明中视为成立的前提条件。在Lean中，`assumption` tactic寻找匹配的假设。

### Axiom (公理)

不加证明而接受的基本命题，作为理论体系的出发点。
> **相关**: [Postulate](#postulate-假定), [Theorem](#theorem-定理)

---

## B

### β-reduction (Beta归约)

λ演算中的基本归约规则：`(λx. M) N → M[x := N]`。
> **相关**: [λ-calculus](#λ-calculus-lambda演算)

### Bi-implication (双蕴含)

逻辑连接词 `↔`，表示"当且仅当"。

### Bijection (双射)

既是单射又是满射的函数，建立集合间的一一对应。
> **相关**: [Injection](#injection-单射), [Surjection](#surjection-满射)

### Binary Relation (二元关系)

集合A上的关系是 A × A 的子集。

### Binary Search Tree (二叉搜索树)

满足左子树 < 根 < 右子树的二叉树结构。

### Binding (绑定)

将变量名与值或类型关联的过程。

### Boolean (布尔)

取值为真(True)或假(False)的逻辑类型。

### Bottom (⊥, 底)

表示矛盾或不可满足的类型/命题。在类型论中是不可实例化的类型。

### By Contradiction (反证法)

证明方法：假设结论不成立，导出矛盾。
> **相关**: [Proof by Contradiction](#proof-by-contradiction-反证法)

---

## C

### Calculus of Constructions (构造演算)

包含高阶多态和依赖类型的λ演算扩展，是Coq和Lean的理论基础。

### Canonical Form (典范形式)

无法进一步归约的项，代表值的标准表示。

### Cardinality (基数)

集合的大小度量。有限集的基数是元素个数，无限集的基数描述其"大小级别"。

### Cartesian Product (笛卡尔积)

集合A和B的笛卡尔积 A × B = {(a, b) | a ∈ A, b ∈ B}。

### Category (范畴)

由对象和态射组成的数学结构，满足结合律和单位元律。
> **相关**: [Functor](#functor-函子), [Natural Transformation](#natural-transformation-自然变换)

### Category Theory (范畴论)

研究范畴及其关系的数学分支，提供统一的抽象框架。

### Certificate (证书)

证明某性质的验证信息，如素性证书、类型检查证书。

### Choice Function (选择函数)

从每个非空集合中选择一个元素的特殊函数。
> **相关**: [Axiom of Choice](#axiom-of-choice-选择公理)

### Church Encoding (邱奇编码)

用λ项编码数据类型的方法。

### Class (类)

- 面向对象：对象的蓝图
- 集合论：真类(proper class)是不能作为集合元素的集合族
- Type Class：定义接口的机制

### Closed Term (闭合项)

不含自由变量的项。
> **相关**: [Free Variable](#free-variable-自由变量)

### Coercion (强制类型转换)

自动的类型转换机制。

### Commutativity (交换律)

运算满足 `a ∘ b = b ∘ a`。

### Compactness (紧致性)

拓扑空间中，任何开覆盖都有有限子覆盖的性质。

### Completeness (完备性)

- 逻辑：所有有效式都可证
- 度量空间：所有柯西序列收敛

### Composition (复合)

函数复合：`(f ∘ g)(x) = f(g(x))`。

### Computability (可计算性)

问题能否由算法解决的性质。

### Confluence (合流性)

归约系统性质：不同归约路径最终收敛到相同结果。
> **相关**: [Church-Rosser](#church-rosser-property-邱奇-罗瑟性质)

### Congruence (同余)

保持等价关系的替换性质。

### Conjunction (合取)

逻辑与 (∧, AND)。

### Consistency (一致性)

理论不蕴含矛盾的性质。

### Constructor (构造子)

归纳类型的引入规则，用于构造该类型的值。
> **相关**: [Inductive Type](#inductive-type-归纳类型)

### Continuity (连续性)

拓扑或分析中"没有突变"的性质。

### Contradiction (矛盾)

命题P与¬P同时成立的状态。

### Contrapositive (逆否命题)

P → Q 的逆否命题是 ¬Q → ¬P，两者逻辑等价。

### Convergence (收敛)

序列或函数趋向于极限的性质。

### Conversion (转换)

在Lean中，定义等价的项可以互相转换。

### Coq

基于构造演算的定理证明器。
> **相关**: [Lean](#lean), [Agda](#agda)

### Curry-Howard Correspondence (柯里-霍华德对应)

命题与类型、证明与程序之间的同构关系。
> **相关**: [Propositions as Types](#propositions-as-types-命题即类型)

---

## D

### Decidable (可判定的)

存在算法能确定命题真假的性质。

```lean
class Decidable (p : Prop) where
  dec : p ∨ ¬p
```

### Decision Procedure (判定过程)

能自动确定问题答案的算法。

### Deduction (演绎)

从一般前提出发得出具体结论的推理方法。
> **相关**: [Induction](#induction-归纳)

### Definitional Equality (定义等价)

通过展开定义和计算可判定的相等性。

### Dependent Function (依赖函数)

返回值类型依赖于参数的函数，即依赖函数类型(Π-type)。

### Dependent Type (依赖类型)

类型可以依赖于值的类型系统。

```lean
Vector α n  -- 类型依赖于长度n
```

### Derivation (推导)

形式系统中证明的语法树结构。

### Disjunction (析取)

逻辑或 (∨, OR)。

### Distributivity (分配律)

`a * (b + c) = a * b + a * c` 等性质。

### Domain (定义域)

函数所有可能输入的集合。
> **相关**: [Codomain](#codomain-陪域), [Range](#range-值域)

### Double Negation (双重否定)

¬¬P 与 P 的关系。在经典逻辑中等价，在构造逻辑中不等价。

### DSL (Domain-Specific Language, 领域特定语言)

为特定应用领域设计的专用语言。

---

## E

### Effect (效应)

超出纯计算的程序行为，如IO、状态、异常。

### Element (元素)

集合的成员。

### Elimination (消去)

归纳类型的消去规则，用于从该类型的值中提取信息。

### Empty Set (∅, 空集)

不含任何元素的集合。

### Empty Type (空类型)

没有值的类型，对应矛盾命题。
> **相关**: [Void](#void-空类型)

### Encoding (编码)

用一种形式系统表示另一种系统的数据或程序。

### Entailment ( entailment, 语义后承)

Γ ⊨ P 表示在所有使Γ为真的解释中P也为真。

### Enumerated Type (枚举类型)

有限个命名值构成的类型。

```lean
inductive Color
  | red | green | blue
```

### Equality (相等)

两个对象相同的数学关系。有不同强度的相等：

- 定义相等 (Definitional Equality)
- 命题相等 (Propositional Equality)

### Equational Reasoning (等式推理)

使用等式链进行证明的方法。

### Equivalence (等价)

自反、对称、传递的关系。

### Equivalence Class (等价类)

等价关系下相互等价的元素组成的集合。

### Equivalence Relation (等价关系)

满足自反性、对称性、传递性的关系。

### Eta-conversion (Eta转换)

λ演算扩展：`(λx. f x)` 与 `f` 的等价(当x不在f中自由出现时)。

### Evaluation (求值)

计算表达式的值。

### Existential Quantifier (∃, 存在量词)

"存在...使得..."的量化。

### Ex Falso Quodlibet (爆炸原理)

从假命题可推出任何命题。

### Expression (表达式)

可求值的语法结构。

### Extensionality (外延性)

由外部行为（而非内部结构）决定相等的性质。
> **相关**: [Function Extensionality](#function-extensionality-函数外延性)

---

## F

### Field (域)

支持加减乘除的代数结构，如 ℚ, ℝ, ℂ。
> **相关**: [Ring](#ring-环), [Group](#group-群)

### Filter (滤子)

拓扑和收敛理论中的工具。

### Finite Set (有限集)

元素个数有限的集合。

### First-Order Logic (一阶逻辑)

量词只能作用于个体（不能作用于谓词或函数）的逻辑系统。
> **相关**: [Higher-Order Logic](#higher-order-logic-高阶逻辑)

### Fixed Point (不动点)

满足 f(x) = x 的点。

### Formal Language (形式语言)

按严格语法规则定义的符号串集合。

### Formal Method (形式化方法)

使用数学技术进行软件和硬件规范、开发和验证的方法。

### Formal Verification (形式化验证)

使用形式化数学方法证明系统正确性。

### Formula (公式)

按语法规则构造的符号串，可解释为命题或谓词。

### Free Variable (自由变量)

未被量词绑定的变量。
> **相关**: [Bound Variable](#bound-variable-约束变量)

### Function (函数)

输入与输出间的确定映射关系。

### Function Extensionality (函数外延性)

若两函数对所有输入产生相同输出，则两函数相等。

### Functional Programming (函数式编程)

以函数为主要构造块的编程范式。

### Functor (函子)

范畴间的结构保持映射。

---

## G

### Galois Connection (伽罗瓦连接)

两个偏序集间的特殊对应关系。

### Generalized Algebraic Data Type (GADT, 广义代数数据类型)

允许构造函数结果类型变化的ADT。

### Generator (生成器)

产生序列值的机制。

### Generic Programming (泛型编程)

编写与具体类型无关的代码。
> **相关**: [Parametric Polymorphism](#parametric-polymorphism-参数多态)

### Girard's Paradox (吉拉尔悖论)

Type : Type 系统的不一致性。

### Goal (目标)

证明中待证的命题。

### Greatest Lower Bound (最大下界/下确界)

偏序集中所有下界中的最大者。
> **相关**: [Least Upper Bound](#least-upper-bound-最小上界上确界)

### Group (群)

满足封闭性、结合律、单位元、逆元的代数结构。

### Group Homomorphism (群同态)

保持群运算的函数。

### Groupoid (广群)

所有态射都是同构的范畴。

---

## H

### Halting Problem (停机问题)

判定程序是否会停机的不可判定问题。

### Hash Map (哈希表)

通过哈希函数实现快速查找的数据结构。

### Higher-Order Function (高阶函数)

以函数为参数或返回函数的函数。

### Higher-Order Logic (HOL, 高阶逻辑)

量词可作用于函数和谓词的逻辑系统。

### Higher-Order Unification (高阶合一)

处理函数类型项的合一算法。

### Homomorphism (同态)

保持代数结构的映射。
> **相关**: [Isomorphism](#isomorphism-同构)

### Hypothesis (假设)

证明开始时引入的前提。

---

## I

### Idempotence (幂等)

运算满足 `f(f(x)) = f(x)`。

### Identity (恒等/单位元)

- 函数：恒等函数 `id(x) = x`
- 代数：单位元 `e ∘ a = a`

### Iff (If and Only If, 当且仅当)

逻辑双条件。

### Image (像)

函数映射结果的集合。

### Implication (蕴含)

逻辑连接词 `→`，"如果...那么..."。

### Impredicativity (非谓词性)

通过包含待定义集合的量化来定义集合。

### Indiscernibility of Identicals (同一的不可分辨性)

相等对象具有相同性质。

### Induction (归纳)

- 数学归纳法：证明对所有自然数成立
- 结构归纳法：证明对归纳类型所有值成立

### Inductive Hypothesis (归纳假设)

归纳证明中假设命题对较小值成立。

### Inductive Step (归纳步骤)

证明命题对n成立时也对n+1成立。

### Inductive Type (归纳类型)

通过构造子归纳定义的类型。

### Infimum (下确界)

最大下界。

### Infix Notation (中缀记法)

运算符放在操作数之间，如 `a + b`。

### Injection (单射)

不同输入映射到不同输出的函数。

### Instance (实例)

- 类型类：具体类型的实现
- 逻辑：特定情形

### Int (整数)

整数类型 ℤ = {..., -2, -1, 0, 1, 2, ...}。

### Integer Programming (整数规划)

变量取整数值的优化问题。

### Interpretation (解释)

给形式语言符号赋予含义。

### Introduction Rule (引入规则)

逻辑连接词的构造规则。
> **相关**: [Elimination Rule](#elimination-rule-消去规则)

### Intuitionistic Logic (直觉主义逻辑)

不接受排中律的构造性逻辑。

### Invariant (不变量)

在程序执行过程中保持的性质。

### Inverse (逆元)

- 加法：相反数
- 乘法：倒数
- 函数：反函数

### Isomorphism (同构)

结构保持的双射。

---

## J

### Judgment (判断)

类型论中关于类型和项的断言，如 `Γ ⊢ t : T`。

### Judgmental Equality (判断相等)

类型论中可直接判定的相等。

---

## K

### Kernel (核心)

定理证明器中进行最终类型检查的小部分可信代码。

### Kleene Star (克林闭包)

语言的所有有限连接构成的集合，记作 L*。

### Kripke Semantics (克里普克语义)

模态逻辑的基于可能世界的语义。

---

## L

### Lambda Abstraction (λ抽象)

创建匿名函数：λx. M。

### Lambda Calculus (λ演算)

研究函数定义、应用和递归的形式系统。

### Lattice (格)

任意两元素有最小上界和最大下界的偏序集。

### Law of Excluded Middle (排中律)

∀P, P ∨ ¬P。经典逻辑接受，构造逻辑拒绝。

### Laziness (惰性求值)

需要时才计算表达式值的策略。
> **相关**: [Strictness](#strictness-严格求值)

### Lean

微软研究院开发的定理证明器和编程语言。

### Lemma (引理)

用于证明定理的辅助命题。
> **相关**: [Theorem](#theorem-定理)

### Lens (透镜)

函数式编程中访问和修改数据结构字段的模式。

### Level (层级)

类型论中避免悖论的宇宙层级。

### Lexicographic Order (字典序)

按字母顺序排列字符串的方式推广。

### Library (库)

可复用的代码集合。

### Linear Order (线性序/全序)

任意两元素可比较的偏序。

### List (列表)

有序的元素序列。

### Logic (逻辑)

研究有效推理的学科。

### Logical Connective (逻辑连接词)

组合命题的运算符，如 ∧, ∨, →, ¬。

### Loop Invariant (循环不变量)

循环中每次迭代都保持的性质。

### Lower Bound (下界)

小于等于集合所有元素的值。

---

## M

### Map (映射)

- 函数的同义词
- 数据结构：关联数组/字典

### Match Expression (匹配表达式)

模式匹配语法结构。

### Mathematical Induction (数学归纳法)

证明对所有自然数成立的方法。

### Maybe Type (Maybe类型)

表示可能有值也可能没有的容器类型，即 `Option`。

### Measure (度量)

用于证明终止性的良基度量。

### Metatheory (元理论)

关于理论的理论。

### Metavariable (元变量)

证明过程中待填充的未知项。

### Method (方法)

面向对象中与对象关联的函数。

### Metric Space (度量空间)

定义了距离函数的集合。

### Mixfix Notation (混合记法)

运算符可以有多个参数位置的记法。

### Modal Logic (模态逻辑)

研究必然性和可能性的逻辑分支。

### Model (模型)

满足一组公理的数学结构。

### Model Checking (模型检测)

自动验证有限状态系统性质的技术。

### Module (模块)

组织代码的单元，包含相关定义和定理。

### Modus Ponens (假言推理)

从 P → Q 和 P 推出 Q 的推理规则。

### Monad (单子)

- 范畴论：自函子范畴的幺半群
- 函数式编程：处理效应的结构

### Monoid (幺半群)

有单位元的半群。

### Morphism (态射)

范畴论中结构保持的映射。

### Multiset (多重集)

允许元素重复的集合推广。

### Mutual Recursion (相互递归)

多个定义相互引用的递归。

---

## N

### Nat (自然数)

非负整数 ℕ = {0, 1, 2, ...}。

### Natural Deduction (自然演绎)

按直觉推导方式组织的逻辑演算。

### Natural Number (自然数)

用于计数的数 0, 1, 2, ...

### Natural Transformation (自然变换)

两个函子之间的结构保持映射族。

### Negation (否定)

逻辑非 (¬, NOT)。

### Normal Form (范式)

标准简化形式的表达式。
> **相关**: [Canonical Form](#canonical-form-典范形式)

### Normalization (规范化)

将表达式转换为范式的过程。

### Notation (记法)

语法糖，提供更易读的语法形式。

---

## O

### Object (对象)

- 面向对象：类的实例
- 范畴论：范畴的成员

### Opaque (不透明)

隐藏内部实现细节的定义。

### Open (打开)

使命名空间内容可直接访问。

### Operator (运算符)

表示运算的特殊符号或函数。

### Option (选项)

表示值可能存在或不存在的数据类型。

```lean
inductive Option (α : Type)
  | none : Option α
  | some : α → Option α
```

### Or (或)

逻辑析取 (∨)。

### Order (序)

元素间的比较关系。

### Ordered Field (有序域)

带有全序关系的域。

### Overloading (重载)

同一符号在不同上下文有不同含义。

---

## P

### Package (包)

组织和分发代码的单元。

### Parametric Polymorphism (参数多态)

对任意类型都适用的定义。

### Partial Function (偏函数)

并非对所有输入都有定义的函数。
> **相关**: [Total Function](#total-function-全函数)

### Partial Order (偏序)

自反、反对称、传递的关系，不要求任意两元素可比。

### Pattern Matching (模式匹配)

根据值的形式进行分支选择。

### Pi-type (Π类型)

依赖函数类型。

### Polymorphism (多态)

代码对多种类型适用的性质。

### Postulate (假定)

作为公理而不加证明接受的命题。

### Powerset (幂集)

集合所有子集的集合，记作 P(A) 或 2^A。

### Precedence (优先级)

运算符结合的优先顺序。

### Predicate (谓词)

返回布尔值的函数，表示性质或关系。

### Predicate Logic (谓词逻辑)

包含量词和谓词的一阶逻辑。

### Prefix Notation (前缀记法)

运算符放在操作数之前，如 `+ a b`。

### Presheaf (预层)

反变函子到集合范畴。

### Primitive Recursion (原始递归)

受限的递归定义形式，保证可计算性。

### Product Type (积类型)

元组类型，如 `A × B`。

### Productivity (生产力)

共同归纳定义生成无限数据的能力。

### Profunctor (预函子)

双变函子，在一个参数逆变，另一个参数协变。

### Proof (证明)

确立命题真理性的论证。

### Proof Assistant (证明助手)

交互式形式化证明的软件工具。

### Proof Irrelevance (证明无关性)

同一命题的所有证明被视为相等。

### Proof Term (证明项)

Curry-Howard对应中，证明作为程序的具体表示。

### Proof by Contradiction (反证法)

假设结论不成立导出矛盾来证明命题。

### Proof by Reflection (反射证明)

将证明问题转化为计算问题的方法。

### Prop (命题)

Lean中命题的宇宙。

### Proposition (命题)

可真可假的陈述句。

### Propositions as Types (命题即类型)

Curry-Howard同构的核心思想。

---

## Q

### Quantifier (量词)

- ∀ 全称量词
- ∃ 存在量词

### Quotient (商)

按等价关系划分集合得到的结构。

### Quotient Type (商类型)

通过等价关系将类型划分的构造。

---

## R

### Range (值域)

函数所有可能输出的集合。

### Real (实数)

实数类型 ℝ。

### Reasoning (推理)

从前提得出结论的思维过程。

### Record (记录)

命名字段的复合数据结构。

### Recursion (递归)

定义引用自身的定义方式。

### Recursive Function (递归函数)

通过递归定义的函数。

### Redex (可约式)

可以进行归约的表达式子项。

### Reduction (归约)

将表达式转换为更简形式。

### Refinement (精化)

逐步添加细节的过程。

### Reflexivity (自反性)

∀a, a = a 的性质。

### Relation (关系)

集合上元素间的联系。

### Rewriting (重写)

使用等式进行替换的操作。

### Ring (环)

支持加减乘的代数结构。

---

## S

### Semantics (语义)

语言表达式含义的研究。

### Semigroup (半群)

满足结合律的代数结构。

### Set (集合)

不重复元素的无序汇集。

### Setoid (集oid)

带有等价关系的集合。

### Set-builder Notation (集合构造记法)

`{x | P(x)}` 描述满足性质P的元素集合。

### Sigma Type (Σ类型)

依赖对类型，Σ(x:A), B(x)。

### Signature (签名)

- 代数结构：运算和常量的描述
- 逻辑：非逻辑符号的集合

### Simplification (简化)

使用重写规则简化表达式。

### Singleton (单例)

只有一个元素的集合或类型。

### Sort (类)

Lean中 Type 和 Prop 的统称。

### Soundness (可靠性)

可证的命题都是有效的。
> **相关**: [Completeness](#completeness-完备性)

### Specification (规范)

系统预期行为的描述。

### State (状态)

系统在特定时刻的完整描述。

### State Monad (状态单子)

处理可变状态的单子。

### Strictness (严格求值)

立即计算参数值的策略。

### String (字符串)

字符序列。

### Strong Induction (强归纳法)

假设对所有小于n的值成立来证明对n成立。

### Structure (结构)

单构造子的归纳类型，用于打包数据。

### Subgoal (子目标)

证明中分解出的待证命题。

### Subgroup (子群)

群的子集且自身构成群。

### Subset (子集)

包含于另一集合的集合。

### Subsingleton (单例类型)

最多有一个值的类型。

### Substitution (替换)

用项替换变量的操作。

### Subtype (子类型)

满足某谓词的类型元素。

### Sufficient Condition (充分条件)

A是B的充分条件：A → B。

### Sum Type (和类型)

互斥联合类型，如 `A ⊕ B` 或 `Either A B`。

### Surjection (满射)

值域等于陪域的函数。

### Symmetry (对称性)

若a = b则b = a 的性质。

### Synthesis (合成)

自动推导隐式参数的过程。

### Syntax (语法)

语言表达式结构的研究。

---

## T

### Tactic (策略)

Lean中修改证明状态的命令。

### Tactic Mode (策略模式)

使用tactics构建证明的风格。

### Term (项)

类型论中表达式的基本单位。

### Term Mode (项模式)

直接构造证明项的风格。

### Terminal Object (终对象)

范畴中到任何对象有唯一态射的对象。

### Termination (终止性)

计算在有限步内完成的性质。

### Theorem (定理)

已被证明的重要命题。

### Theory (理论)

一组公理及其逻辑后承。

### Top (⊤, 顶)

- 偏序集中的最大元
- 类型论中的平凡真命题
- 格论中的最大元

### Total Function (全函数)

对所有输入都有定义的函数。

### Totality (全性)

函数对所有输入都有定义的性质。

### Transitivity (传递性)

若a = b且b = c则a = c 的性质。

### Tree (树)

层次数据结构。

### Tuple (元组)

固定长度的有序元素组。

### Type (类型)

值的分类。

### Type Class (类型类)

定义接口和实现多态的机制。

### Type Constructor (类型构造子)

从类型构造新类型的运算。

### Type Hierarchy (类型层级)

类型间的包含或子类型关系。

### Type Inference (类型推断)

自动推导表达式类型的过程。

### Type Safety (类型安全)

良类型程序不会陷入未定义行为。

### Type Scheme (类型方案)

多态类型的表示。

### Type System (类型系统)

语言中类型规则和检查机制的集合。

### Type Theory (类型论)

研究类型系统的数学理论。

### Type Universe (类型宇宙)

类型的类型，如 `Type`, `Type 1`, `Prop`。

### Typing Judgment (类型判断)

`Γ ⊢ t : T` 表示在上下文Γ中t具有类型T。

---

## U

### Unification (合一)

寻找使表达式相等的替换的过程。

### Union (并集)

集合A ∪ B = {x | x ∈ A 或 x ∈ B}。

### Unit (单位类型)

只有一个值的类型，记作 `()` 或 `unit`。

### Universe (宇宙)

包含类型的类型，用于避免悖论。

### Universe Polymorphism (宇宙多态)

定义对所有宇宙层级都适用。

### Universal Quantifier (∀, 全称量词)

"对所有..."的量化。

### Upper Bound (上界)

大于等于集合所有元素的值。

---

## V

### Vacuously True (空虚真)

因前提永不满足而为真的蕴含式。

### Validity (有效性)

在所有解释下都为真的性质。

### Value (值)

表达式的计算结果。

### Variable (变量)

可代表不同值的符号。

### Variance (变型)

类型参数在子类型关系中的行为：

- 协变(covariant)
- 逆变(contravariant)
- 不变(invariant)

### Vector (向量)

- 数学：有方向的量
- 类型论：定长列表

### Void (空类型)

没有值的类型。

---

## W

### Weak Head Normal Form (弱头范式)

不是可约式或λ抽象的表达式。

### Weakening (弱化)

在上下文中添加额外假设仍成立。

### Well-Founded (良基的)

没有无限降链的关系，保证递归终止。

### Well-Founded Recursion (良基递归)

基于良基关系的递归定义。

### Well-Typed (良类型的)

满足类型系统规则的表达式。

### Witness (证据)

存在量词证明中的具体值。

---

## X

### Xor (异或)

逻辑运算符，一方为真另一方为假时为真。

---

## Y

### Yoneda Lemma (米田引理)

范畴论中的基本定理，描述可表函子。

---

## Z

### ZFC

Zermelo-Fraenkel集合论加选择公理，数学基础标准形式。

### Zero (零)

- 数字：加法单位元
- 范畴论：终对象或始对象

---

## 附录: 缩写速查

| 缩写 | 全称 | 中文 |
|-----|------|-----|
| ADT | Algebraic Data Type | 代数数据类型 |
| ATP | Automated Theorem Proving | 自动定理证明 |
| CIC | Calculus of Inductive Constructions | 归纳构造演算 |
| DSL | Domain-Specific Language | 领域特定语言 |
| GADT | Generalized Algebraic Data Type | 广义代数数据类型 |
| HOL | Higher-Order Logic | 高阶逻辑 |
| ITP | Interactive Theorem Proving | 交互式定理证明 |
| LCF | Logic for Computable Functions | 可计算函数逻辑 |
| ML | Meta Language | 元语言 |
| REPL | Read-Eval-Print Loop | 交互式解释器 |
| TCB | Trusted Computing Base | 可信计算基 |
| UDT | Universe of Discourse Type | 论域类型 |

---

> 📚 **术语总数**: 200+
>
> 💡 **建议**: 使用搜索功能(Ctrl+F)快速查找特定术语。
