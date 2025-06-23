# 形式语用学 (Formal Pragmatics)

## 1. 形式语用学概述

形式语用学结合形式语义学和语用学的研究方法，使用数学工具对语言使用的语境依赖性和动态特性进行严格形式化表示。本文档提供形式语用学的主要理论框架，并给出相应的计算实现。

### 1.1 核心问题

形式语用学致力于回答以下核心问题：

1. 如何形式化表示语境及其变化？
2. 语境更新如何影响话语意义的解释？
3. 对话如何作为动态、互动和策略性过程进行建模？
4. 言语行为的效力如何用形式化方法刻画？
5. 语用推理如何被形式化并计算？

## 2. 动态语义学 (Dynamic Semantics)

### 2.1 上下文变化潜力 (Context Change Potentials)

动态语义学将句子意义视为上下文变化潜力（CCP）。

#### 2.1.1 形式化表示

```text
⟦S⟧ = λc.c'
```

其中：
- c 是初始上下文
- c' 是更新后的上下文
- λc.c' 是将上下文映射到新上下文的函数

### 2.2 文件卡语义学 (File Card Semantics)

文件卡语义学将上下文建模为包含命名实体的信息卡片。

```text
c = {x₁:D₁, x₂:D₂, ..., xₙ:Dₙ}
```

其中：
- xᵢ 是话语指代物（如"一个男人"引入的实体）
- Dᵢ 是关于指代物xᵢ的描述信息

### 2.3 更新语义学操作

```text
⟦S₁;S₂⟧(c) = ⟦S₂⟧(⟦S₁⟧(c))  // 顺序组合
⟦∃x.φ⟧(c) = c ∪ {x:φ}      // 引入新指代物
⟦φ(x)⟧(c) = c[x/φ]         // 更新已有指代物信息
```

### 2.4 照应和指代

```text
⟦代词⟧(c) = λP.P(选择(可用指代物(c)))
```

其中 `选择` 是根据语法、语义和语用线索选择合适指代物的函数。

## 3. 对话游戏理论 (Dialogue Game Theory)

### 3.1 对话作为博弈

对话可以建模为参与者之间的策略博弈。

```text
对话游戏 G = <P, M, R, U>
```

其中：
- P 是参与者集合
- M 是可能的话语行为集合
- R 是对话规则
- U 是效用函数，评估对话状态对各参与者的价值

### 3.2 对话游戏中的策略

```text
策略σ_i : H → Δ(M_i)
```

其中：
- H 是对话历史
- M_i 是参与者i可选择的话语行为
- Δ(M_i) 是M_i上的概率分布
- σ_i 是从对话历史到话语行为选择的映射

### 3.3 最优对话策略

```text
σ*_i = argmax_{σ_i} 期望效用(σ_i, σ*_{-i})
```

其中：
- σ*_i 是参与者i的最优策略
- σ*_{-i} 是其他参与者的最优策略
- 期望效用是基于策略组合的预期收益

## 4. 信息状态更新 (Information State Update)

### 4.1 信息状态表示

```text
IS = <私有信念, 共享信念, 对话承诺, 对话计划, 对话历史>
```

### 4.2 更新规则

```text
更新(IS, 话语) = IS'
```

更新规则示例：

```text
如果 话语 = 断言(p) 且 发话者 = i 则
    IS' = IS + {
        共享信念 += p,
        对话承诺 += (i, p),
        对话历史 += 断言(i, p)
    }
```

### 4.3 对话推进

```text
推进条件(IS, 话语) = {
    相关性(话语, IS.对话历史),
    一致性(话语, IS.共享信念),
    有效性(话语, IS.对话计划)
}
```

## 5. 言语行为形式化 (Formal Speech Acts)

### 5.1 动态言语行为

言语行为可以表示为信息状态更新函数：

```text
assert(p) = λIS.IS[共享信念/共享信念∪{p}]
request(A) = λIS.IS[对话承诺/对话承诺∪{(听话者, A)}]
question(p) = λIS.IS[对话计划/对话计划∪{回答(p)}]
```

### 5.2 权限和义务

```text
权限(agent, action) = authorized(agent, action) ∈ IS.共享信念
义务(agent, action) = obligated(agent, action) ∈ IS.对话承诺
```

### 5.3 言语行为成功条件的动态表示

```text
成功(act) ↔ ∀c(预设(act)(c) → 定义域(CCP(act))(c))
```

## 6. Rust 代码实现

```rust
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;

/// 话语引用物（discourse referent）
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Referent {
    id: String,
    properties: HashSet<String>,
}

/// 信息状态
#[derive(Debug, Clone)]
pub struct InformationState<A> {
    // 共同基础（共享信念）
    common_ground: HashSet<String>,
    // 对话承诺
    commitments: HashMap<A, HashSet<String>>,
    // 对话计划（问题在讨论中，待解决议题等）
    agenda: VecDeque<String>,
    // 话语引用物存储
    discourse_referents: HashMap<String, Referent>,
    // 对话历史
    history: Vec<String>,
}

impl<A: Clone + Eq + Hash + Debug> InformationState<A> {
    /// 创建新的信息状态
    pub fn new() -> Self {
        Self {
            common_ground: HashSet::new(),
            commitments: HashMap::new(),
            agenda: VecDeque::new(),
            discourse_referents: HashMap::new(),
            history: Vec::new(),
        }
    }
    
    /// 更新共同基础
    pub fn update_common_ground(&mut self, proposition: &str) {
        self.common_ground.insert(proposition.to_string());
    }
    
    /// 添加对话承诺
    pub fn add_commitment(&mut self, agent: &A, proposition: &str) {
        self.commitments
            .entry(agent.clone())
            .or_insert_with(HashSet::new)
            .insert(proposition.to_string());
    }
    
    /// 添加对话议题
    pub fn add_agenda_item(&mut self, item: &str) {
        self.agenda.push_back(item.to_string());
    }
    
    /// 处理断言
    pub fn process_assertion(&mut self, speaker: &A, content: &str) {
        // 更新信息状态
        self.update_common_ground(content);
        self.add_commitment(speaker, content);
        self.history.push(format!("{:?} 断言: {}", speaker, content));
    }
}
```

## 7. 对话游戏代码实现

```rust
/// 对话行为类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DialogueMove {
    Assert(String),
    Question(String),
    Answer(String, String),  // 问题, 回答
    Request(String),
    Accept(String),
    Reject(String),
}

/// 对话游戏表示
pub struct DialogueGame<A> {
    // 参与者
    participants: Vec<A>,
    // 当前对话状态
    state: InformationState<A>,
    // 轮到谁说话
    turn: usize,
    // 对话规则
    rules: Vec<Box<dyn Fn(&DialogueMove, &InformationState<A>) -> bool>>,
}

impl<A: Clone + Eq + Hash + Debug> DialogueGame<A> {
    /// 创建新的对话游戏
    pub fn new(
        participants: Vec<A>,
        rules: Vec<Box<dyn Fn(&DialogueMove, &InformationState<A>) -> bool>>,
    ) -> Self {
        Self {
            participants,
            state: InformationState::new(),
            turn: 0,
            rules,
        }
    }
    
    /// 检查对话行为是否满足规则
    pub fn check_move(&self, mv: &DialogueMove) -> bool {
        self.rules.iter().all(|rule| rule(mv, &self.state))
    }
    
    /// 执行对话行为
    pub fn make_move(&mut self, player: usize, mv: DialogueMove) -> Result<(), String> {
        // 检查是否是该玩家的回合
        if player != self.turn {
            return Err("不是该玩家的回合".to_string());
        }
        
        // 检查行为是否符合规则
        if !self.check_move(&mv) {
            return Err("行为不符合对话规则".to_string());
        }
        
        // 更新对话状态
        match &mv {
            DialogueMove::Assert(content) => {
                self.state.update_common_ground(content);
                self.state.add_commitment(&self.participants[player], content);
            },
            DialogueMove::Question(content) => {
                self.state.add_agenda_item(content);
            },
            _ => {}  // 简化实现，略去其他情况处理
        }
        
        // 更新轮次
        self.turn = (self.turn + 1) % self.participants.len();
        
        Ok(())
    }
}
```

## 8. 形式语用学的应用

### 8.1 语境依赖表达式处理

形式语用学为处理语境依赖表达式提供框架，特别是在：
- 照应和指代解析
- 定冠词和代词语义处理
- 预设投射的计算
- 语境更新效果的追踪

### 8.2 对话系统设计

在对话系统开发中，形式语用学用于：
- 信息状态管理
- 对话行为规划
- 上下文表示和更新
- 共享信念跟踪

### 8.3 交互式故事生成

形式语用学支持交互式故事生成：
- 话语引用物的引入和追踪
- 角色视角的形式化表示
- 故事情节发展的动态模型
- 读者期望的预测与管理

## 9. 相关领域联系

### 9.1 与形式语义学的关系

形式语用学与形式语义学密切相关：
- 静态语义与动态语义的整合
- 模型论与更新语义的结合
- 语境参数与内容区分
- 语境敏感表达式分析

### 9.2 与博弈论的联系

形式语用学借鉴博弈论框架：
- 对话作为策略互动
- 最优对话策略分析
- 合作与非合作对话建模
- 信息不对称处理

## 10. 参考文档

- [语言哲学总览](./README.md)
- [语义学理论](./01_Semantics.md)
- [语用学理论](./02_Pragmatics.md)
- [语言行为理论](./03_Speech_Acts.md) 