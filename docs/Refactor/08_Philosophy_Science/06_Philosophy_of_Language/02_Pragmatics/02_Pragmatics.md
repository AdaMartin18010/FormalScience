# 语用学 (Pragmatics)

## 1. 语用学概述

语用学研究语言在使用情境中的含义，关注超出字面语义的内容，包括会话含义、言外之意、语境依赖性等方面。本文档提供语用学理论的系统性形式化表示，并给出相应的计算实现。

### 1.1 核心问题

语用学理论致力于回答以下核心问题：

1. 语言使用者如何在特定语境中传达超出字面含义的信息？
2. 会话含义如何从字面含义衍生？
3. 语境如何影响语言表达式的解释？
4. 言语行为如何在交际中发挥功能？
5. 会话互动如何遵循特定规则？

## 2. 会话含义理论 (Conversational Implicature)

### 2.1 格莱斯会话含义

格莱斯区分了"所说"（字面含义）和"所含蕴"（会话含义）。

#### 2.1.1 形式化表示

```text
字面含义: ⟦S⟧ = p
会话含义: impl(S, C) = q
```

其中：

- S 是话语
- p 是字面含义命题
- q 是会话含义命题
- C 是会话语境
- impl 是会话含义推导函数

### 2.2 会话含义计算

会话含义可通过以下步骤计算：

```text
impl(S, C) = q iff
  (1) 说话者说了 S，字面含义为 p
  (2) 假设说话者遵循合作原则和会话准则
  (3) 若只传达 p 则违背准则
  (4) 说话者能够且知道应当传达 q
  (5) 说话者期望听话者能够推导出 q
  (6) 说话者无意阻止听话者推导 q
```

### 2.3 会话含义类型

```text
一般会话含义: impl_gen(S, C) = q
  • 不依赖特定语境特征
  • 默认出现，除非被取消

特殊会话含义: impl_part(S, C) = q
  • 依赖特定语境特征
  • 需要特定背景假设
```

## 3. 合作原则与会话准则 (Cooperative Principle and Maxims)

### 3.1 合作原则

```text
合作原则: 在会话中的贡献应符合会话目的或方向
```

### 3.2 会话准则形式化

#### 3.2.1 质量准则 (Quality)

```text
Q(S, C) = true iff
  (1) 说话者不说假信息
  (2) 说话者有充分证据支持所说
```

#### 3.2.2 量准则 (Quantity)

```text
QN(S, C) = true iff
  (1) 说话者的贡献信息量适中
  (2) 不提供超过所需的信息
```

#### 3.2.3 关联准则 (Relevance)

```text
R(S, C) = true iff
  S 与当前会话目标和方向相关
```

#### 3.2.4 方式准则 (Manner)

```text
M(S, C) = true iff
  (1) 避免表达晦涩
  (2) 避免歧义
  (3) 简洁
  (4) 有序
```

### 3.3 准则违背与会话含义

```text
若 ¬X(S, C) 且说话者遵循合作原则，则存在 q 使得:
  (1) q 为真使得 X(S + q, C) = true
  (2) 说话者期望听话者知道 (1)
  (3) impl(S, C) = q
```

其中 X 是某个会话准则。

## 4. 语用预设 (Pragmatic Presupposition)

### 4.1 预设定义

预设是说话者认为与听话者共享的背景信息。

```text
P 是 S 在语境 C 中的预设 iff
  (1) 说话者假设 P 为真
  (2) 说话者假设听话者知道 P 为真
  (3) 说话者假设听话者知道说话者假设 P 为真
```

### 4.2 预设触发语

```text
预设触发: trigger(S) = {P₁, P₂, ..., Pₙ}
```

常见预设触发语包括：

- 确定描述
- 事实性动词
- 变化状态动词
- 再次/也/仍然等副词
- 分裂句结构

### 4.3 预设投射问题

```text
proj(P, φ(S)) = true iff P ∈ presup(φ(S))
```

其中：

- P 是预设
- S 是触发预设的句子
- φ 是嵌套算子（如否定、条件、问句等）
- proj 是预设投射函数
- presup 是获取句子预设集的函数

## 5. 语境敏感性 (Context Sensitivity)

### 5.1 语境参数

```text
语境 C = <s, a, t, l, w>
```

其中：

- s 是说话者
- a 是听话者
- t 是时间
- l 是地点
- w 是可能世界

### 5.2 语境依赖表达式

```text
⟦我⟧_C = s
⟦你⟧_C = a
⟦现在⟧_C = t
⟦这里⟧_C = l
⟦实际上⟧_C = λp.p(w)
```

### 5.3 语境更新

```text
C + S = C'
```

其中：

- C 是初始语境
- S 是话语
- C' 是更新后的语境
- '+' 是语境更新函数

## 6. Rust 代码实现

### 6.1 会话含义实现

```rust
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::fmt::Debug;

/// 语境表示
#[derive(Clone, Debug)]
pub struct Context<S, A, T, L, W> {
    speaker: S,
    addressee: A,
    time: T,
    location: L,
    world: W,
    common_ground: HashSet<String>,
    conversation_goal: String,
}

/// 会话含义系统
pub struct ConversationalImplicature<S, A, T, L, W> {
    contexts: HashMap<String, Context<S, A, T, L, W>>,
    literal_meanings: HashMap<String, String>,
}

impl<S, A, T, L, W> ConversationalImplicature<S, A, T, L, W>
where
    S: Clone + Eq + Hash + Debug,
    A: Clone + Eq + Hash + Debug,
    T: Clone + Eq + Hash + Debug,
    L: Clone + Eq + Hash + Debug,
    W: Clone + Eq + Hash + Debug,
{
    /// 创建新的会话含义系统
    pub fn new() -> Self {
        Self {
            contexts: HashMap::new(),
            literal_meanings: HashMap::new(),
        }
    }
    
    /// 添加语境
    pub fn add_context(&mut self, id: &str, context: Context<S, A, T, L, W>) {
        self.contexts.insert(id.to_string(), context);
    }
    
    /// 添加字面含义
    pub fn add_literal_meaning(&mut self, utterance: &str, meaning: &str) {
        self.literal_meanings.insert(utterance.to_string(), meaning.to_string());
    }
    
    /// 检查质量准则是否满足
    pub fn check_quality_maxim(&self, utterance: &str, context_id: &str) -> bool {
        // 实际应用中需要检查说话者的信念状态
        // 这里简化处理
        true
    }
    
    /// 检查数量准则是否满足
    pub fn check_quantity_maxim(&self, utterance: &str, context_id: &str) -> bool {
        // 实际应用中需要比较信息量
        // 这里简化处理
        true
    }
    
    /// 检查关联准则是否满足
    pub fn check_relevance_maxim(&self, utterance: &str, context_id: &str) -> bool {
        if let (Some(context), Some(meaning)) = (
            self.contexts.get(context_id),
            self.literal_meanings.get(utterance)
        ) {
            // 检查与会话目标的相关性
            meaning.contains(&context.conversation_goal)
        } else {
            false
        }
    }
    
    /// 检查方式准则是否满足
    pub fn check_manner_maxim(&self, utterance: &str) -> bool {
        // 实际应用中需要检查表达的简洁性、明确性等
        // 这里简化处理
        !utterance.contains("可能") && !utterance.contains("或许")
    }
    
    /// 计算会话含义
    pub fn compute_implicature(&self, utterance: &str, context_id: &str) -> Vec<String> {
        let mut implicatures = Vec::new();
        
        // 检查各项准则，生成可能的会话含义
        if !self.check_quantity_maxim(utterance, context_id) {
            implicatures.push("说话者无法提供更多信息".to_string());
        }
        
        if !self.check_relevance_maxim(utterance, context_id) {
            implicatures.push("说话者想改变话题".to_string());
        }
        
        if !self.check_manner_maxim(utterance) {
            implicatures.push("说话者对信息的确定性不高".to_string());
        }
        
        implicatures
    }
}
```

### 6.2 语用预设实现

```rust
/// 预设处理系统
pub struct PresuppositionSystem {
    triggers: HashMap<String, Vec<String>>,
    projection_rules: HashMap<String, Box<dyn Fn(Vec<String>) -> Vec<String>>>,
}

impl PresuppositionSystem {
    /// 创建新的预设处理系统
    pub fn new() -> Self {
        Self {
            triggers: HashMap::new(),
            projection_rules: HashMap::new(),
        }
    }
    
    /// 添加预设触发语
    pub fn add_trigger(&mut self, expression: &str, presuppositions: Vec<&str>) {
        self.triggers.insert(
            expression.to_string(),
            presuppositions.into_iter().map(|s| s.to_string()).collect()
        );
    }
    
    /// 计算句子的预设
    pub fn compute_presuppositions(&self, sentence: &str) -> Vec<String> {
        let mut presuppositions = Vec::new();
        
        // 检查触发语
        for (trigger, trigger_presups) in &self.triggers {
            if sentence.contains(trigger) {
                presuppositions.extend(trigger_presups.clone());
            }
        }
        
        // 处理复合句中的预设投射
        if sentence.contains("如果") && sentence.contains("那么") {
            // 条件句处理：部分预设可能被过滤
            // 简化处理
            presuppositions.retain(|p| !p.contains("存在"));
        }
        
        presuppositions
    }
}
```

## 7. 语用学的应用

### 7.1 对话系统开发

语用学理论为对话系统提供基础，特别是在：

- 理解言外之意
- 生成符合语境的回应
- 维护会话连贯性
- 处理语境依赖表达

### 7.2 语用推理系统

在计算语用学中，语用理论用于构建：

- 会话含义推理引擎
- 预设检测系统
- 语境敏感表达解析器
- 语用歧义消解系统

### 7.3 跨文化交际

语用学为跨文化交际研究提供：

- 文化特定准则差异分析
- 跨文化语用失误预测
- 语用能力评估框架

## 8. 相关领域联系

### 8.1 与语义学的关系

语用学与语义学在以下方面有密切联系：

- 语义-语用界面
- 语境依赖语义vs.语用含义
- 预设vs.蕴含区分
- 字面意义与衍生意义

### 8.2 与语言行为理论的联系

语用学为语言行为理论提供：

- 会话含义作为非直接言语行为基础
- 言语行为成功条件的语境依赖性
- 语用推理机制

## 9. 参考文档

- [语言哲学总览](./README.md)
- [语义学理论](./01_Semantics.md)
- [语言行为理论](./03_Speech_Acts.md)
- [形式语用学](./04_Formal_Pragmatics.md)
