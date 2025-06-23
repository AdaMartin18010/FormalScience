# 语言行为理论 (Speech Acts Theory)

## 1. 语言行为理论概述

语言行为理论研究语言作为行动的本质，关注说话者如何通过言语行为执行各种社会功能。本文档提供语言行为理论的系统性形式化表示，并给出相应的计算实现。

### 1.1 核心问题

语言行为理论致力于回答以下核心问题：

1. 语言如何用于执行行动而非仅描述事实？
2. 言语行为的成功条件是什么？
3. 不同类型的言语行为如何区分？
4. 言语行为的力量如何确定？
5. 间接言语行为如何理解？

## 2. 言语行为分类 (Speech Acts Classification)

### 2.1 基本言语行为分析

言语行为可分为三个层次：

#### 2.1.1 形式化表示

```text
言语行为 = <L, I, P>
```

其中：

- L 是言内行为（说出某些话）
- I 是言外行为（通过说话执行特定意图）
- P 是言后行为（话语对听者产生的效果）

### 2.2 塞尔言语行为分类

塞尔(Searle)将言语行为分为五大类：

```text
言语行为类型 = {断言型, 指令型, 承诺型, 表情型, 宣告型}
```

#### 2.2.1 断言型言语行为 (Assertives)

```text
断言(p) = 说话者使听话者相信p为真
断言力量 = <说话者对p的信念强度, 证据强度>
```

例如：陈述、描述、断言、预测等。

#### 2.2.2 指令型言语行为 (Directives)

```text
指令(A) = 说话者尝试使听话者执行A
指令力量 = <说话者权威程度, 紧急程度, 执行必要性>
```

例如：请求、命令、建议、问题等。

#### 2.2.3 承诺型言语行为 (Commissives)

```text
承诺(A) = 说话者承诺将来执行A
承诺力量 = <承诺约束性, 时间限制, 条件限制>
```

例如：承诺、保证、誓言、威胁等。

#### 2.2.4 表情型言语行为 (Expressives)

```text
表情(S,p) = 说话者表达关于p的心理状态S
表情力量 = <情感强度, 真诚程度>
```

例如：感谢、祝贺、道歉、问候等。

#### 2.2.5 宣告型言语行为 (Declarations)

```text
宣告(p) = 说话者通过宣告p使p成为事实
宣告力量 = <说话者制度权力, 制度条件满足度>
```

例如：宣战、任命、解雇、命名、宣判等。

## 3. 言语行为成功条件 (Felicity Conditions)

### 3.1 一般成功条件

言语行为成功需满足以下条件：

```text
成功条件 = <预备条件, 真诚条件, 本质条件>
```

### 3.2 特定言语行为的成功条件

#### 3.2.1 承诺行为的成功条件

```text
预备条件(承诺(A)) = 听话者希望A发生 ∧ 说话者能够执行A
真诚条件(承诺(A)) = 说话者有意执行A
本质条件(承诺(A)) = 说话者有义务执行A
```

#### 3.2.2 请求行为的成功条件

```text
预备条件(请求(A)) = 听话者能够执行A
真诚条件(请求(A)) = 说话者希望A发生
本质条件(请求(A)) = 说话者试图让听话者执行A
```

#### 3.2.3 断言行为的成功条件

```text
预备条件(断言(p)) = 说话者有证据证明p
真诚条件(断言(p)) = 说话者相信p为真
本质条件(断言(p)) = 说话者承诺p为真
```

## 4. 间接言语行为 (Indirect Speech Acts)

### 4.1 基本形式

间接言语行为通过一种言语行为间接执行另一种言语行为。

```text
间接言语行为 = <F1(p), F2(q), C>
```

其中：

- F1 是直接执行的言语行为类型
- p 是直接言语行为的命题内容
- F2 是间接执行的言语行为类型
- q 是间接言语行为的命题内容
- C 是语境

### 4.2 间接言语行为识别

识别间接言语行为的过程：

```text
识别(F1(p), C) → F2(q) iff
  (1) 说话者表面执行F1(p)
  (2) F1(p)在C中不满足关联准则或其他准则
  (3) 存在F2(q)在C中满足准则
  (4) 说话者有通过F1(p)执行F2(q)的意图
```

### 4.3 典型间接言语行为模式

```text
能力疑问句 → 请求: "你能关窗吗？" → 请求(关窗)
意愿陈述句 → 请求: "我想要水。" → 请求(给水)
理由疑问句 → 批评: "为什么房间这么乱？" → 批评(房间太乱)
```

## 5. 会话含义与言语行为的关系

言语行为与会话含义的交互：

```text
Conv_impl(F(p), C) = F'(q) iff
  (1) 说话者使用F(p)
  (2) 根据C和合作原则，F'(q)更合适
  (3) 说话者期望听话者识别F'(q)
```

## 6. Rust 代码实现

### 6.1 言语行为系统

```rust
/// 言语行为类型枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpeechActType {
    Assertive,
    Directive,
    Commissive,
    Expressive,
    Declaration,
}

/// 成功条件结构
pub struct FelicityCondition {
    preparatory: Vec<String>,
    sincerity: Vec<String>,
    essential: String,
}

/// 言语行为表示
pub struct SpeechAct {
    act_type: SpeechActType,
    propositional_content: String,
    speaker: String,
    addressee: String,
    felicity_conditions: FelicityCondition,
    force: u8, // 1-100的强度值
}

impl SpeechAct {
    /// 创建新的言语行为
    pub fn new(
        act_type: SpeechActType,
        content: &str,
        speaker: &str,
        addressee: &str,
        force: u8,
    ) -> Self {
        // 根据言语行为类型生成适当的成功条件
        let conditions = match act_type {
            SpeechActType::Assertive => FelicityCondition {
                preparatory: vec![format!("{} 有证据支持 {}", speaker, content)],
                sincerity: vec![format!("{} 相信 {}", speaker, content)],
                essential: format!("{} 承诺 {} 为真", speaker, content),
            },
            SpeechActType::Directive => FelicityCondition {
                preparatory: vec![format!("{} 能够执行 {}", addressee, content)],
                sincerity: vec![format!("{} 希望 {} 执行 {}", speaker, addressee, content)],
                essential: format!("{} 试图让 {} 执行 {}", speaker, addressee, content),
            },
            SpeechActType::Commissive => FelicityCondition {
                preparatory: vec![
                    format!("{} 能够执行 {}", speaker, content),
                    format!("{} 希望 {} 执行 {}", addressee, speaker, content),
                ],
                sincerity: vec![format!("{} 有意执行 {}", speaker, content)],
                essential: format!("{} 承诺执行 {}", speaker, content),
            },
            SpeechActType::Expressive => FelicityCondition {
                preparatory: vec![format!("{} 相关于 {}", content, speaker)],
                sincerity: vec![format!("{} 有特定情感关于 {}", speaker, content)],
                essential: format!("{} 表达情感关于 {}", speaker, content),
            },
            SpeechActType::Declaration => FelicityCondition {
                preparatory: vec![format!("{} 有权力宣告 {}", speaker, content)],
                sincerity: vec![],  // 宣告不需要真诚条件
                essential: format!("{} 宣告 {} 并因此使之成为事实", speaker, content),
            },
        };

        Self {
            act_type,
            propositional_content: content.to_string(),
            speaker: speaker.to_string(),
            addressee: addressee.to_string(),
            felicity_conditions: conditions,
            force,
        }
    }
    
    /// 检查言语行为是否满足成功条件
    pub fn check_felicity(&self, context: &Context) -> bool {
        // 实际应用中需要根据上下文检查每个条件
        // 这里简化实现
        true
    }
    
    /// 执行言语行为的效果
    pub fn perform(&self, context: &mut Context) -> Result<(), String> {
        if !self.check_felicity(context) {
            return Err("言语行为不满足成功条件".to_string());
        }
        
        // 根据言语行为类型产生不同效果
        match self.act_type {
            SpeechActType::Assertive => {
                // 将命题内容添加到共同认知
                context.add_to_common_ground(&self.propositional_content);
            },
            SpeechActType::Directive => {
                // 创建听话者的行为义务
                context.add_obligation(&self.addressee, &self.propositional_content);
            },
            SpeechActType::Commissive => {
                // 创建说话者的行为承诺
                context.add_commitment(&self.speaker, &self.propositional_content);
            },
            SpeechActType::Expressive => {
                // 记录说话者的情感状态
                context.record_emotion(&self.speaker, &self.propositional_content);
            },
            SpeechActType::Declaration => {
                // 改变世界状态
                context.change_world_state(&self.propositional_content);
            }
        }
        
        Ok(())
    }
}

/// 简化的语境表示
pub struct Context {
    common_ground: HashSet<String>,
    obligations: HashMap<String, Vec<String>>,
    commitments: HashMap<String, Vec<String>>,
    emotions: HashMap<String, Vec<String>>,
    world_state: HashSet<String>,
}

impl Context {
    // 各种语境操作方法...
    pub fn add_to_common_ground(&mut self, proposition: &str) {
        self.common_ground.insert(proposition.to_string());
    }
    
    pub fn add_obligation(&mut self, agent: &str, action: &str) {
        self.obligations.entry(agent.to_string())
            .or_insert_with(Vec::new)
            .push(action.to_string());
    }
    
    pub fn add_commitment(&mut self, agent: &str, action: &str) {
        self.commitments.entry(agent.to_string())
            .or_insert_with(Vec::new)
            .push(action.to_string());
    }
    
    pub fn record_emotion(&mut self, agent: &str, emotion: &str) {
        self.emotions.entry(agent.to_string())
            .or_insert_with(Vec::new)
            .push(emotion.to_string());
    }
    
    pub fn change_world_state(&mut self, fact: &str) {
        self.world_state.insert(fact.to_string());
    }
}
```

### 6.2 间接言语行为处理系统

```rust
/// 间接言语行为识别系统
pub struct IndirectSpeechActRecognizer {
    // 语境信息
    context: Context,
    // 间接言语行为模式库
    patterns: HashMap<(SpeechActType, String), (SpeechActType, String)>,
}

impl IndirectSpeechActRecognizer {
    /// 创建新的识别系统
    pub fn new(context: Context) -> Self {
        let mut patterns = HashMap::new();
        
        // 添加常见间接言语行为模式
        patterns.insert(
            (SpeechActType::Assertive, "能力陈述".to_string()),
            (SpeechActType::Directive, "请求".to_string())
        );
        
        patterns.insert(
            (SpeechActType::Directive, "理由疑问".to_string()),
            (SpeechActType::Assertive, "批评".to_string())
        );
        
        Self { context, patterns }
    }
    
    /// 识别间接言语行为
    pub fn recognize(&self, direct_act: &SpeechAct) -> Option<SpeechAct> {
        // 检查是否有匹配的间接言语行为模式
        let pattern_key = (direct_act.act_type, self.classify_pattern(&direct_act.propositional_content));
        
        if let Some((indirect_type, indirect_function)) = self.patterns.get(&pattern_key) {
            // 创建识别的间接言语行为
            let indirect_content = self.derive_indirect_content(
                &direct_act.propositional_content, 
                indirect_function
            );
            
            Some(SpeechAct::new(
                *indirect_type,
                &indirect_content,
                &direct_act.speaker,
                &direct_act.addressee,
                direct_act.force
            ))
        } else {
            None
        }
    }
    
    // 对语句进行模式分类
    fn classify_pattern(&self, content: &str) -> String {
        if content.starts_with("你能") || content.starts_with("您能") {
            "能力陈述".to_string()
        } else if content.starts_with("为什么") {
            "理由疑问".to_string()
        } else {
            "其他".to_string()
        }
    }
    
    // 从直接行为内容推导间接行为内容
    fn derive_indirect_content(&self, direct_content: &str, indirect_function: &str) -> String {
        match indirect_function {
            "请求" => {
                // 将"你能关窗吗"转换为"关窗"
                direct_content.replace("你能", "").replace("吗", "").trim().to_string()
            },
            "批评" => {
                // 将"为什么房间这么乱"转换为"房间不应该这么乱"
                direct_content.replace("为什么", "不应该").trim().to_string()
            },
            _ => direct_content.to_string()
        }
    }
}
```

## 7. 语言行为理论的应用

### 7.1 人机对话系统

语言行为理论为人机对话系统提供基础，特别是在：

- 意图识别
- 对话管理
- 语境追踪
- 社交反应生成

### 7.2 法律语言分析

在法律语境中，语言行为理论用于分析：

- 合同和承诺的约束力
- 法律宣告的效力
- 证词的断言性质
- 法律文本的解释

### 7.3 社交人工智能

对于社交AI系统，语言行为理论提供：

- 适当言语行为选择机制
- 社交义务追踪
- 礼貌策略
- 语言适应机制

## 8. 相关领域联系

### 8.1 与语用学的联系

语言行为理论与语用学密切相关：

- 会话含义与间接言语行为
- 语境敏感性
- 合作原则的共享
- 交际意图推理

### 8.2 与社会语言学的联系

语言行为理论为社会语言学提供：

- 文化特定言语行为分析
- 权力关系对言语行为的影响
- 礼貌理论基础
- 社会角色与言语行为选择

## 9. 参考文档

- [语言哲学总览](./README.md)
- [语用学理论](./02_Pragmatics.md)
- [形式语用学](./04_Formal_Pragmatics.md)
- [伦理学中的规范性语言](../08_Ethics/01_Normative_Ethics.md)
