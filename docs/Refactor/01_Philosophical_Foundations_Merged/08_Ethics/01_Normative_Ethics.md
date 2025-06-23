# 规范伦理学 (Normative Ethics)

## 📋 1. 概述

规范伦理学是伦理学的核心分支，研究什么样的行为是道德的、什么样的行为是不道德的，并试图建立判断行为道德性的一般性标准。本文档从形式科学的角度分析三大主要规范伦理学理论：功利主义、义务论和德性伦理学，为它们提供形式化的表达和计算实现。

## 🎯 2. 规范伦理学的核心问题

规范伦理学试图回答以下核心问题：

1. 什么使行为在道德上是正确的？
2. 道德评价的基础是什么？
3. 道德判断如何适用于不同情境？
4. 如何权衡不同的道德价值？

## 📚 3. 核心理论形式化

### 3.1 功利主义

功利主义认为，行为的道德价值取决于其结果产生的效用或福利。

#### 3.1.1 基本原理

功利主义的核心原则可形式化为：

$$
Right(A) \iff \forall B \in Actions, Utility(A) \geq Utility(B)
$$

其中：

- $Right(A)$ 表示行为 $A$ 在道德上是正确的
- $Actions$ 表示所有可能行为的集合
- $Utility(X)$ 表示行为 $X$ 产生的总效用

#### 3.1.2 效用计算

效用计算公式：

$$
Utility(A) = \sum_{i=1}^{n} w_i \times Welfare_i(A)
$$

其中：

- $n$ 是受影响个体的数量
- $w_i$ 是个体 $i$ 的权重
- $Welfare_i(A)$ 是行为 $A$ 对个体 $i$ 的福利影响

#### 3.1.3 变体形式化

1. **行为功利主义**：每个具体行为应最大化效用

    $$
    Right(A) \iff Utility(A) = \max_{X \in Actions} Utility(X)
    $$

2. **规则功利主义**：遵循能最大化效用的规则

    $$
    Right(A) \iff A \text{ 符合规则 } R \land R \in \arg\max_{R' \in Rules} Utility(Society(R'))
    $$

3. **偏好功利主义**：满足偏好而非仅考虑快乐

    $$
    Utility(A) = \sum_{i=1}^{n} w_i \times PreferenceSatisfaction_i(A)
    $$

### 3.2 义务论

义务论认为，行为的道德价值取决于行为本身的特性，而不是其结果。

#### 3.2.1 基本原理

康德的绝对命令可形式化为：

$$
Right(A) \iff Universalizable(A) \land RespectsPerson(A)
$$

其中：

- $Universalizable(A)$ 表示行为 $A$ 的准则可以不自相矛盾地被普遍化
- $RespectsPerson(A)$ 表示行为 $A$ 尊重人的尊严，将人视为目的而非手段

#### 3.2.2 道德规则系统

义务论构建形式化道德规则系统：

$$
MoralSystem = \langle P, D, R \rangle
$$

其中：

- $P$ 是道德原则集合
- $D$ 是道德义务集合
- $R$ 是道德推理规则集合

#### 3.2.3 道德冲突解决

义务论中冲突解决可表示为：

$$
Priority(D_i, D_j, C) = \begin{cases}
1 & \text{如果义务 } D_i \text{ 在情境 } C \text{ 中优先于 } D_j \\
0 & \text{如果义务 } D_j \text{ 在情境 } C \text{ 中优先于 } D_i \\
undefined & \text{如果义务不可比较}
\end{cases}
$$

### 3.3 德性伦理学

德性伦理学关注行为主体的品格特质，而非单一行为或规则。

#### 3.3.1 基本原理

德性伦理学可形式化为：

$$
Right(A, P) \iff Virtuous(P) \land InAccordanceWithVirtue(A, P)
$$

其中：

- $P$ 表示行为主体
- $Virtuous(P)$ 表示主体 $P$ 具有德性
- $InAccordanceWithVirtue(A, P)$ 表示行为 $A$ 符合主体 $P$ 的德性

#### 3.3.2 德性空间

德性可在多维空间中表示：

$$
VirtueSpace = \langle V_1, V_2, ..., V_n \rangle
$$

其中每个 $V_i$ 代表一种德性维度，每个人可表示为此空间中的一个点。

#### 3.3.3 德性与中道

亚里士多德的中道理论可形式化为：

$$
Virtue_i = Mean(Excess_i, Deficiency_i)
$$

其中：

- $Virtue_i$ 是第 $i$ 种德性
- $Excess_i$ 是过度的极端
- $Deficiency_i$ 是不足的极端

## 🔍 4. 理论比较与综合

### 4.1 形式化比较框架

三种理论可在统一框架下比较：

$$
Evaluation(T, A, C) = \langle Consistency(T), Intuitiveness(T, A, C), Applicability(T, C) \rangle
$$

其中：

- $T$ 是道德理论
- $A$ 是行为
- $C$ 是情境
- $Consistency(T)$ 测量理论的内部一致性
- $Intuitiveness(T, A, C)$ 测量理论判断与直觉的吻合度
- $Applicability(T, C)$ 测量理论在情境中的适用性

### 4.2 理论综合

整合方法可形式化为：

$$
IntegratedJudgment(A) = \alpha \times Utilitarian(A) + \beta \times Deontological(A) + \gamma \times Virtue(A)
$$

其中：

- $\alpha, \beta, \gamma$ 是权重参数，且 $\alpha + \beta + \gamma = 1$
- $Utilitarian(A)$、$Deontological(A)$ 和 $Virtue(A)$ 分别是三种理论对行为 $A$ 的评价

## 💻 5. 计算实现

以下代码实现了规范伦理学的核心概念：

```rust
// 基础类型定义
pub type AgentId = u64;
pub type ActionId = u64;
pub type ContextId = u64;
pub type Utility = f64;

// 道德理论特征
pub trait MoralTheory {
    fn evaluate(&self, action: &Action, context: &Context) -> MoralEvaluation;
    fn is_right(&self, action: &Action, context: &Context) -> bool;
    fn rank_actions(&self, actions: &[Action], context: &Context) -> Vec<(ActionId, MoralEvaluation)>;
    fn resolve_dilemma(&self, actions: &[Action], context: &Context) -> ActionId;
}

// 功利主义实现
pub struct Utilitarianism {
    pub weight_fn: Box<dyn Fn(AgentId, ContextId) -> f64>,
}

impl MoralTheory for Utilitarianism {
    fn evaluate(&self, action: &Action, context: &Context) -> MoralEvaluation {
        let mut total_utility = 0.0;
        
        for agent in context.affected_agents() {
            let weight = (self.weight_fn)(agent.id, context.id);
            let welfare = action.welfare_impact(agent.id, context);
            total_utility += weight * welfare;
        }
        
        MoralEvaluation {
            theory: "Utilitarianism".to_string(),
            value: total_utility,
            classification: if total_utility > 0.0 { "Right" } else { "Wrong" }.to_string(),
            justification: format!("行为产生总效用: {}", total_utility),
        }
    }
    
    fn is_right(&self, action: &Action, context: &Context) -> bool {
        // 一个行为是正确的，当且仅当没有其他可行行为产生更高的效用
        let this_utility = self.evaluate(action, context).value;
        
        for alt_action in context.available_actions() {
            if alt_action.id != action.id {
                let alt_utility = self.evaluate(&alt_action, context).value;
                if alt_utility > this_utility {
                    return false;
                }
            }
        }
        
        true
    }
    
    // 其余方法实现略
}

// 义务论实现
pub struct Deontology {
    pub principles: Vec<MoralPrinciple>,
    pub priority_matrix: HashMap<(PrincipleId, PrincipleId), i32>,
}

impl MoralTheory for Deontology {
    fn evaluate(&self, action: &Action, context: &Context) -> MoralEvaluation {
        // 检查行为是否符合道德原则
        let violations = self.principles.iter()
            .filter(|p| !p.is_respected_by(action, context))
            .collect::<Vec<_>>();
            
        let is_permissible = violations.is_empty();
        
        MoralEvaluation {
            theory: "Deontology".to_string(),
            value: if is_permissible { 1.0 } else { -1.0 },
            classification: if is_permissible { "Right" } else { "Wrong" }.to_string(),
            justification: if is_permissible {
                "行为符合所有道德原则".to_string()
            } else {
                format!("行为违反原则: {}", 
                    violations.iter()
                        .map(|p| p.name.clone())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            },
        }
    }
    
    // 其余方法实现略
}

// 德性伦理学实现
pub struct VirtueEthics {
    pub virtues: Vec<Virtue>,
    pub virtue_thresholds: HashMap<VirtueId, f64>,
}

impl MoralTheory for VirtueEthics {
    fn evaluate(&self, action: &Action, context: &Context) -> MoralEvaluation {
        // 评估行为是否展现了德性
        let mut virtue_scores = Vec::new();
        
        for virtue in &self.virtues {
            let score = virtue.exhibited_in(action, context);
            virtue_scores.push((virtue.id, score));
        }
        
        let avg_virtue = virtue_scores.iter()
            .map(|(_, score)| *score)
            .sum::<f64>() / virtue_scores.len() as f64;
            
        MoralEvaluation {
            theory: "Virtue Ethics".to_string(),
            value: avg_virtue,
            classification: if avg_virtue >= 0.5 { "Right" } else { "Wrong" }.to_string(),
            justification: format!("行为展现德性平均分: {:.2}", avg_virtue),
        }
    }
    
    // 其余方法实现略
}

// 综合伦理评估系统
pub struct IntegratedEthics {
    pub utilitarian: Utilitarianism,
    pub deontological: Deontology, 
    pub virtue_ethics: VirtueEthics,
    pub weights: (f64, f64, f64), // (功利主义权重, 义务论权重, 德性伦理权重)
}

impl MoralTheory for IntegratedEthics {
    fn evaluate(&self, action: &Action, context: &Context) -> MoralEvaluation {
        let util_eval = self.utilitarian.evaluate(action, context);
        let deont_eval = self.deontological.evaluate(action, context);
        let virtue_eval = self.virtue_ethics.evaluate(action, context);
        
        let integrated_value = 
            self.weights.0 * util_eval.value + 
            self.weights.1 * deont_eval.value + 
            self.weights.2 * virtue_eval.value;
            
        MoralEvaluation {
            theory: "Integrated Ethics".to_string(),
            value: integrated_value,
            classification: if integrated_value > 0.0 { "Right" } else { "Wrong" }.to_string(),
            justification: format!(
                "综合评估:\n功利: {:.2} (权重: {:.2})\n义务: {:.2} (权重: {:.2})\n德性: {:.2} (权重: {:.2})",
                util_eval.value, self.weights.0,
                deont_eval.value, self.weights.1,
                virtue_eval.value, self.weights.2
            ),
        }
    }
    
    // 其余方法实现略
}
```

## 📊 6. 案例分析

### 6.1 电车问题形式化

电车问题可形式化为：

$$
Trolley = \langle A_{divert}, A_{nothing}, Lives(Track1), Lives(Track2) \rangle
$$

三种伦理理论的评价：

$$
\begin{align}
Utilitarian(A_{divert}) &= 1 \times Lives(Track1) - 5 \times Lives(Track2) \\
Deontological(A_{divert}) &= Violates(DoNoHarm) \land Violates(UseAsEnd) \\
Virtue(A_{divert}) &= Compassion(save5) - Ruthlessness(kill1)
\end{align}
$$

### 6.2 复杂案例：自动驾驶伦理决策

自动驾驶决策可形式化为：

$$
AutonomousDecision = \langle A_{options}, Risks, Values, Constraints \rangle
$$

各理论的集成：

$$
Decision = \argmax_{A \in A_{options}} \left( \alpha U(A) + \beta D(A) + \gamma V(A) \right)
$$

其中：

- $U(A)$ 是功利主义评分
- $D(A)$ 是义务论评分
- $V(A)$ 是德性伦理评分
- $\alpha, \beta, \gamma$ 是权重

## 🔗 7. 交叉引用

- [元伦理学](./02_Meta_Ethics.md) - 伦理学的元理论基础
- [应用伦理学](./03_Applied_Ethics.md) - 规范伦理学的具体应用
- [AI伦理学](./04_AI_Ethics.md) - AI系统中的道德决策
- [认识论](../02_Epistemology/README.md) - 道德知识的认识论基础

## 📚 8. 参考文献

1. Bentham, J. (1789). *An Introduction to the Principles of Morals and Legislation*
2. Kant, I. (1785). *Groundwork for the Metaphysics of Morals*
3. Aristotle. (c. 350 BCE). *Nicomachean Ethics*
4. Mill, J. S. (1863). *Utilitarianism*
5. Ross, W. D. (1930). *The Right and the Good*
6. Hursthouse, R. (1999). *On Virtue Ethics*
7. Rawls, J. (1971). *A Theory of Justice*
8. Parfit, D. (1984). *Reasons and Persons*
9. Korsgaard, C. M. (1996). *The Sources of Normativity*
10. Scanlon, T. M. (1998). *What We Owe to Each Other*
