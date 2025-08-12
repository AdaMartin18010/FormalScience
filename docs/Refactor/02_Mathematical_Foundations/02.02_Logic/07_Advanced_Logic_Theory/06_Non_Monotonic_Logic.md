# 非单调逻辑理论

## 概述

非单调逻辑是经典逻辑的重要扩展，专门用于处理推理中的不确定性、例外情况和知识更新。它提供了处理默认推理、封闭世界假设、异常处理等领域的强大工具，在人工智能、知识表示、常识推理等领域有重要应用。

## 基本概念

### 非单调性

#### 1. 单调性与非单调性

**定义 6.1** (单调性)
经典逻辑是单调的，即如果 $\Gamma \vdash \phi$ 且 $\Gamma \subseteq \Delta$，则 $\Delta \vdash \phi$。

**定义 6.2** (非单调性)
非单调逻辑允许推理结论在添加新信息时被撤销，即可能存在 $\Gamma \vdash \phi$ 但 $\Gamma \cup \{\psi\} \not\vdash \phi$。

#### 2. 非单调推理的特征

**特征 6.1** (非单调推理特征)
非单调推理具有以下特征：

- **可撤销性**: 结论可能被新信息撤销
- **不确定性**: 推理基于不完全信息
- **例外处理**: 能够处理异常情况
- **常识推理**: 模拟人类的常识推理

### 默认逻辑

#### 1. 默认规则

**定义 6.3** (默认规则)
默认规则的形式为：
$$\frac{\alpha : \beta_1, \ldots, \beta_n}{\gamma}$$

其中：
- $\alpha$ 是前提 (prerequisite)
- $\beta_1, \ldots, \beta_n$ 是正当化条件 (justifications)
- $\gamma$ 是结论 (conclusion)

#### 2. 默认理论

**定义 6.4** (默认理论)
默认理论是一个二元组 $\Delta = (D, W)$，其中：
- $D$ 是默认规则集合
- $W$ 是一阶逻辑公式集合

#### 3. 扩展

**定义 6.5** (扩展)
设 $\Delta = (D, W)$ 为默认理论，$E$ 为一阶逻辑公式集合，则 $E$ 是 $\Delta$ 的扩展当且仅当：
$$E = \bigcup_{i=0}^{\infty} E_i$$

其中：
- $E_0 = W$
- $E_{i+1} = \text{Th}(E_i) \cup \{\gamma \mid \frac{\alpha : \beta_1, \ldots, \beta_n}{\gamma} \in D, \alpha \in E_i, \neg\beta_1, \ldots, \neg\beta_n \notin E\}$

### 封闭世界假设

#### 1. 封闭世界假设

**定义 6.6** (封闭世界假设)
封闭世界假设 (CWA) 假设所有不在知识库中的原子公式都为假。

**形式化**: 对于原子公式 $p$，如果 $KB \not\vdash p$，则 $KB \vdash \neg p$

#### 2. 开放世界假设

**定义 6.7** (开放世界假设)
开放世界假设 (OWA) 假设知识库中的信息是不完整的。

**形式化**: 如果 $KB \not\vdash p$ 且 $KB \not\vdash \neg p$，则 $p$ 的真值未知

#### 3. 局部封闭世界假设

**定义 6.8** (局部封闭世界假设)
局部封闭世界假设 (LCWA) 只对特定的谓词应用封闭世界假设。

**形式化**: 对于谓词 $P$，如果 $KB \not\vdash P(\vec{t})$，则 $KB \vdash \neg P(\vec{t})$

### 异常处理

#### 1. 异常逻辑

**定义 6.9** (异常逻辑)
异常逻辑通过引入异常谓词来处理例外情况：

**异常规则**: $\forall x.(P(x) \land \neg Ab(x) \rightarrow Q(x))$
**异常断言**: $Ab(c)$ 表示 $c$ 是异常情况

#### 2. 异常继承

**定义 6.10** (异常继承)
异常继承允许异常情况在层次结构中传播：

**继承规则**: $\forall x.(Bird(x) \land \neg Ab_1(x) \rightarrow Fly(x))$
**异常继承**: $\forall x.(Penguin(x) \rightarrow Ab_1(x))$

### 非单调推理系统

#### 1. 自动认识逻辑

**定义 6.11** (自动认识逻辑)
自动认识逻辑通过模态算子 $L$ 表示"已知"：

**公理**:
- $L\phi \rightarrow \phi$ (真理性)
- $L\phi \rightarrow LL\phi$ (正内省)
- $\neg L\phi \rightarrow L\neg L\phi$ (负内省)

#### 2. 最小模型语义

**定义 6.12** (最小模型语义)
最小模型语义选择信息量最少的模型：

**定义**: 模型 $M$ 是理论 $T$ 的最小模型，当且仅当不存在 $M' \subset M$ 使得 $M' \models T$

#### 3. 优先语义

**定义 6.13** (优先语义)
优先语义通过偏好关系选择最优模型：

**定义**: 模型 $M$ 优先于模型 $M'$，记作 $M \prec M'$，当且仅当 $M$ 在某些方面优于 $M'$

### 非单调推理算法

#### 1. 默认推理算法

**算法 6.1** (默认推理)
输入：默认理论 $\Delta = (D, W)$
输出：扩展 $E$

1. 初始化 $E_0 = W$
2. 对于 $i \geq 0$，计算 $E_{i+1}$：
   - 找到适用的默认规则 $\frac{\alpha : \beta_1, \ldots, \beta_n}{\gamma}$
   - 检查 $\alpha \in E_i$ 且 $\neg\beta_1, \ldots, \neg\beta_n \notin E$
   - 如果适用，将 $\gamma$ 添加到 $E_{i+1}$
3. 重复直到没有新的公式可以添加
4. 返回 $E = \bigcup_{i=0}^{\infty} E_i$

#### 2. 异常处理算法

**算法 6.2** (异常处理)
输入：理论 $T$ 和异常规则
输出：异常处理后的理论

1. 识别潜在的异常情况
2. 应用异常规则
3. 检查一致性
4. 如果发现冲突，选择最具体的规则
5. 返回处理后的理论

## 应用实例

### 常识推理

#### 鸟类飞行推理

```python
# 常识推理系统
class CommonsenseReasoning:
    def __init__(self):
        self.knowledge_base = []
        self.default_rules = []
        self.exceptions = []
    
    def add_knowledge(self, statement):
        """添加知识"""
        self.knowledge_base.append(statement)
    
    def add_default_rule(self, prerequisite, justifications, conclusion):
        """添加默认规则"""
        self.default_rules.append({
            'prerequisite': prerequisite,
            'justifications': justifications,
            'conclusion': conclusion
        })
    
    def add_exception(self, entity, property):
        """添加异常"""
        self.exceptions.append((entity, property))
    
    def default_reasoning(self, entity, property):
        """默认推理"""
        # 检查是否有直接知识
        for statement in self.knowledge_base:
            if statement == f"{property}({entity})":
                return True
            elif statement == f"not {property}({entity})":
                return False
        
        # 检查异常
        for exception_entity, exception_property in self.exceptions:
            if exception_entity == entity and exception_property == property:
                return False
        
        # 应用默认规则
        for rule in self.default_rules:
            if rule['conclusion'] == f"{property}({entity})":
                # 检查前提
                if self.check_prerequisite(rule['prerequisite'], entity):
                    # 检查正当化条件
                    if all(not self.check_justification(just, entity) 
                           for just in rule['justifications']):
                        return True
        
        return None  # 未知
    
    def check_prerequisite(self, prerequisite, entity):
        """检查前提"""
        if prerequisite == "Bird":
            return self.is_bird(entity)
        return False
    
    def check_justification(self, justification, entity):
        """检查正当化条件"""
        if justification.startswith("not "):
            prop = justification[4:]
            return not self.has_property(entity, prop)
        return self.has_property(entity, justification)
    
    def is_bird(self, entity):
        """检查是否为鸟类"""
        return entity in ["tweety", "polly", "penguin"]
    
    def has_property(self, entity, property):
        """检查是否有属性"""
        for statement in self.knowledge_base:
            if statement == f"{property}({entity})":
                return True
        return False

# 使用示例
reasoning = CommonsenseReasoning()

# 添加知识
reasoning.add_knowledge("Bird(tweety)")
reasoning.add_knowledge("Bird(polly)")
reasoning.add_knowledge("Bird(penguin)")

# 添加默认规则：鸟类通常能飞
reasoning.add_default_rule("Bird", ["not cannot_fly"], "can_fly")

# 添加异常：企鹅不能飞
reasoning.add_exception("penguin", "can_fly")

# 推理
print(f"Tweety can fly: {reasoning.default_reasoning('tweety', 'can_fly')}")
print(f"Polly can fly: {reasoning.default_reasoning('polly', 'can_fly')}")
print(f"Penguin can fly: {reasoning.default_reasoning('penguin', 'can_fly')}")
```

### 知识表示

#### 非单调知识库

```python
# 非单调知识库系统
class NonMonotonicKnowledgeBase:
    def __init__(self):
        self.facts = set()
        self.rules = []
        self.defaults = []
        self.exceptions = set()
    
    def add_fact(self, fact):
        """添加事实"""
        self.facts.add(fact)
    
    def add_rule(self, premises, conclusion):
        """添加规则"""
        self.rules.append((premises, conclusion))
    
    def add_default(self, prerequisite, justifications, conclusion):
        """添加默认规则"""
        self.defaults.append({
            'prerequisite': prerequisite,
            'justifications': justifications,
            'conclusion': conclusion
        })
    
    def add_exception(self, exception):
        """添加异常"""
        self.exceptions.add(exception)
    
    def query(self, query):
        """查询"""
        # 首先检查事实
        if query in self.facts:
            return True
        
        # 检查异常
        if query in self.exceptions:
            return False
        
        # 应用规则
        for premises, conclusion in self.rules:
            if conclusion == query:
                if all(self.query(premise) for premise in premises):
                    return True
        
        # 应用默认规则
        for default in self.defaults:
            if default['conclusion'] == query:
                if self.query(default['prerequisite']):
                    if all(not self.query(just) for just in default['justifications']):
                        return True
        
        return None  # 未知
    
    def update_knowledge(self, new_fact):
        """更新知识"""
        # 检查是否与现有知识冲突
        if f"not {new_fact}" in self.facts:
            # 处理冲突
            self.resolve_conflict(new_fact)
        else:
            self.facts.add(new_fact)
    
    def resolve_conflict(self, new_fact):
        """解决冲突"""
        # 简化的冲突解决：优先新知识
        if f"not {new_fact}" in self.facts:
            self.facts.remove(f"not {new_fact}")
        self.facts.add(new_fact)

# 使用示例
kb = NonMonotonicKnowledgeBase()

# 添加事实
kb.add_fact("Bird(tweety)")
kb.add_fact("Bird(penguin)")

# 添加规则
kb.add_rule(["Bird(x)"], "can_fly(x)")

# 添加默认规则
kb.add_default("Bird(x)", ["not cannot_fly(x)"], "can_fly(x)")

# 添加异常
kb.add_exception("can_fly(penguin)")

# 查询
print(f"Tweety can fly: {kb.query('can_fly(tweety)')}")
print(f"Penguin can fly: {kb.query('can_fly(penguin)')}")

# 更新知识
kb.update_knowledge("cannot_fly(tweety)")
print(f"After update - Tweety can fly: {kb.query('can_fly(tweety)')}")
```

### 异常处理

#### 异常继承系统

```python
# 异常继承系统
class ExceptionInheritanceSystem:
    def __init__(self):
        self.hierarchy = {}
        self.properties = {}
        self.exceptions = {}
    
    def add_class(self, class_name, superclass=None):
        """添加类"""
        self.hierarchy[class_name] = superclass
        self.properties[class_name] = set()
        self.exceptions[class_name] = set()
    
    def add_property(self, class_name, property_name):
        """添加属性"""
        if class_name in self.properties:
            self.properties[class_name].add(property_name)
    
    def add_exception(self, class_name, property_name):
        """添加异常"""
        if class_name in self.exceptions:
            self.exceptions[class_name].add(property_name)
    
    def has_property(self, instance, class_name, property_name):
        """检查是否有属性"""
        # 检查直接异常
        if class_name in self.exceptions and property_name in self.exceptions[class_name]:
            return False
        
        # 检查直接属性
        if class_name in self.properties and property_name in self.properties[class_name]:
            return True
        
        # 检查继承
        if class_name in self.hierarchy and self.hierarchy[class_name]:
            superclass = self.hierarchy[class_name]
            return self.has_property(instance, superclass, property_name)
        
        return False
    
    def get_all_properties(self, class_name):
        """获取所有属性"""
        properties = set()
        
        # 添加直接属性
        if class_name in self.properties:
            properties.update(self.properties[class_name])
        
        # 添加继承属性
        if class_name in self.hierarchy and self.hierarchy[class_name]:
            superclass = self.hierarchy[class_name]
            inherited_properties = self.get_all_properties(superclass)
            properties.update(inherited_properties)
        
        # 移除异常
        if class_name in self.exceptions:
            properties.difference_update(self.exceptions[class_name])
        
        return properties

# 使用示例
system = ExceptionInheritanceSystem()

# 定义类层次结构
system.add_class("Animal")
system.add_class("Bird", "Animal")
system.add_class("Penguin", "Bird")

# 添加属性
system.add_property("Animal", "breathes")
system.add_property("Bird", "flies")
system.add_property("Bird", "lays_eggs")

# 添加异常
system.add_exception("Penguin", "flies")

# 检查属性
print(f"Penguin flies: {system.has_property('penguin', 'Penguin', 'flies')}")
print(f"Penguin lays eggs: {system.has_property('penguin', 'Penguin', 'lays_eggs')}")
print(f"Penguin breathes: {system.has_property('penguin', 'Penguin', 'breathes')}")

# 获取所有属性
print(f"Penguin properties: {system.get_all_properties('Penguin')}")
```

## 代码实现

### Rust实现

```rust
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct DefaultRule {
    pub prerequisite: String,
    pub justifications: Vec<String>,
    pub conclusion: String,
}

#[derive(Debug, Clone)]
pub struct DefaultTheory {
    pub rules: Vec<DefaultRule>,
    pub facts: HashSet<String>,
}

impl DefaultTheory {
    pub fn new() -> Self {
        DefaultTheory {
            rules: Vec::new(),
            facts: HashSet::new(),
        }
    }
    
    pub fn add_rule(&mut self, prerequisite: &str, justifications: Vec<String>, conclusion: &str) {
        self.rules.push(DefaultRule {
            prerequisite: prerequisite.to_string(),
            justifications,
            conclusion: conclusion.to_string(),
        });
    }
    
    pub fn add_fact(&mut self, fact: &str) {
        self.facts.insert(fact.to_string());
    }
}

// 非单调推理器
pub struct NonMonotonicReasoner {
    theory: DefaultTheory,
    exceptions: HashSet<String>,
}

impl NonMonotonicReasoner {
    pub fn new(theory: DefaultTheory) -> Self {
        NonMonotonicReasoner {
            theory,
            exceptions: HashSet::new(),
        }
    }
    
    pub fn add_exception(&mut self, exception: &str) {
        self.exceptions.insert(exception.to_string());
    }
    
    pub fn compute_extension(&self) -> HashSet<String> {
        let mut extension = self.theory.facts.clone();
        let mut changed = true;
        
        while changed {
            changed = false;
            
            for rule in &self.theory.rules {
                // 检查前提
                if !self.satisfies_prerequisite(&rule.prerequisite, &extension) {
                    continue;
                }
                
                // 检查正当化条件
                if !self.satisfies_justifications(&rule.justifications, &extension) {
                    continue;
                }
                
                // 检查异常
                if self.exceptions.contains(&rule.conclusion) {
                    continue;
                }
                
                // 添加结论
                if extension.insert(rule.conclusion.clone()) {
                    changed = true;
                }
            }
        }
        
        extension
    }
    
    fn satisfies_prerequisite(&self, prerequisite: &str, extension: &HashSet<String>) -> bool {
        extension.contains(prerequisite)
    }
    
    fn satisfies_justifications(&self, justifications: &[String], extension: &HashSet<String>) -> bool {
        justifications.iter().all(|just| {
            if just.starts_with("not ") {
                let prop = &just[4..];
                !extension.contains(prop)
            } else {
                extension.contains(just)
            }
        })
    }
    
    pub fn query(&self, query: &str) -> Option<bool> {
        let extension = self.compute_extension();
        
        if extension.contains(query) {
            Some(true)
        } else if extension.contains(&format!("not {}", query)) {
            Some(false)
        } else {
            None
        }
    }
}

// 异常处理系统
pub struct ExceptionHandler {
    hierarchy: HashMap<String, Option<String>>,
    properties: HashMap<String, HashSet<String>>,
    exceptions: HashMap<String, HashSet<String>>,
}

impl ExceptionHandler {
    pub fn new() -> Self {
        ExceptionHandler {
            hierarchy: HashMap::new(),
            properties: HashMap::new(),
            exceptions: HashMap::new(),
        }
    }
    
    pub fn add_class(&mut self, class_name: &str, superclass: Option<&str>) {
        self.hierarchy.insert(class_name.to_string(), superclass.map(|s| s.to_string()));
        self.properties.insert(class_name.to_string(), HashSet::new());
        self.exceptions.insert(class_name.to_string(), HashSet::new());
    }
    
    pub fn add_property(&mut self, class_name: &str, property_name: &str) {
        if let Some(props) = self.properties.get_mut(class_name) {
            props.insert(property_name.to_string());
        }
    }
    
    pub fn add_exception(&mut self, class_name: &str, property_name: &str) {
        if let Some(excs) = self.exceptions.get_mut(class_name) {
            excs.insert(property_name.to_string());
        }
    }
    
    pub fn has_property(&self, class_name: &str, property_name: &str) -> bool {
        // 检查直接异常
        if let Some(excs) = self.exceptions.get(class_name) {
            if excs.contains(property_name) {
                return false;
            }
        }
        
        // 检查直接属性
        if let Some(props) = self.properties.get(class_name) {
            if props.contains(property_name) {
                return true;
            }
        }
        
        // 检查继承
        if let Some(superclass) = self.hierarchy.get(class_name) {
            if let Some(superclass_name) = superclass {
                return self.has_property(superclass_name, property_name);
            }
        }
        
        false
    }
    
    pub fn get_all_properties(&self, class_name: &str) -> HashSet<String> {
        let mut properties = HashSet::new();
        
        // 添加直接属性
        if let Some(props) = self.properties.get(class_name) {
            properties.extend(props.clone());
        }
        
        // 添加继承属性
        if let Some(superclass) = self.hierarchy.get(class_name) {
            if let Some(superclass_name) = superclass {
                let inherited = self.get_all_properties(superclass_name);
                properties.extend(inherited);
            }
        }
        
        // 移除异常
        if let Some(excs) = self.exceptions.get(class_name) {
            for exc in excs {
                properties.remove(exc);
            }
        }
        
        properties
    }
}

// 示例使用
fn main() {
    // 创建默认理论
    let mut theory = DefaultTheory::new();
    
    // 添加事实
    theory.add_fact("Bird(tweety)");
    theory.add_fact("Bird(penguin)");
    
    // 添加默认规则
    theory.add_rule("Bird(x)", vec!["not cannot_fly(x)".to_string()], "can_fly(x)");
    
    // 创建推理器
    let mut reasoner = NonMonotonicReasoner::new(theory);
    
    // 添加异常
    reasoner.add_exception("can_fly(penguin)");
    
    // 推理
    println!("Tweety can fly: {:?}", reasoner.query("can_fly(tweety)"));
    println!("Penguin can fly: {:?}", reasoner.query("can_fly(penguin)"));
    
    // 异常处理
    let mut handler = ExceptionHandler::new();
    
    // 定义类层次结构
    handler.add_class("Animal", None);
    handler.add_class("Bird", Some("Animal"));
    handler.add_class("Penguin", Some("Bird"));
    
    // 添加属性
    handler.add_property("Animal", "breathes");
    handler.add_property("Bird", "flies");
    handler.add_property("Bird", "lays_eggs");
    
    // 添加异常
    handler.add_exception("Penguin", "flies");
    
    // 检查属性
    println!("Penguin flies: {}", handler.has_property("Penguin", "flies"));
    println!("Penguin lays eggs: {}", handler.has_property("Penguin", "lays_eggs"));
    println!("Penguin properties: {:?}", handler.get_all_properties("Penguin"));
}
```

### Haskell实现

```haskell
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

-- 默认规则类型
data DefaultRule = DefaultRule
    { prerequisite :: String
    , justifications :: [String]
    , conclusion :: String
    } deriving (Show, Eq)

-- 默认理论类型
data DefaultTheory = DefaultTheory
    { rules :: [DefaultRule]
    , facts :: Set String
    } deriving (Show)

-- 非单调推理器类型
data NonMonotonicReasoner = NonMonotonicReasoner
    { theory :: DefaultTheory
    , exceptions :: Set String
    } deriving (Show)

-- 异常处理器类型
data ExceptionHandler = ExceptionHandler
    { hierarchy :: Map String (Maybe String)
    , properties :: Map String (Set String)
    , exceptions :: Map String (Set String)
    } deriving (Show)

-- 构造函数
defaultTheory :: DefaultTheory
defaultTheory = DefaultTheory [] Set.empty

nonMonotonicReasoner :: DefaultTheory -> NonMonotonicReasoner
nonMonotonicReasoner = NonMonotonicReasoner Set.empty

exceptionHandler :: ExceptionHandler
exceptionHandler = ExceptionHandler Map.empty Map.empty Map.empty

-- 默认理论操作
addRule :: String -> [String] -> String -> DefaultTheory -> DefaultTheory
addRule prereq justs concl theory = 
    theory { rules = DefaultRule prereq justs concl : rules theory }

addFact :: String -> DefaultTheory -> DefaultTheory
addFact fact theory = 
    theory { facts = Set.insert fact (facts theory) }

-- 非单调推理器操作
addException :: String -> NonMonotonicReasoner -> NonMonotonicReasoner
addException exception reasoner = 
    reasoner { exceptions = Set.insert exception (exceptions reasoner) }

computeExtension :: NonMonotonicReasoner -> Set String
computeExtension reasoner = 
    let initialExtension = facts (theory reasoner)
        iterateExtension ext = 
            let newExt = applyRules (rules (theory reasoner)) ext (exceptions reasoner)
            in if newExt == ext then ext else iterateExtension newExt
    in iterateExtension initialExtension

applyRules :: [DefaultRule] -> Set String -> Set String -> Set String
applyRules rules extension exceptions = 
    foldl (\ext rule -> 
        if isRuleApplicable rule extension exceptions
        then Set.insert (conclusion rule) ext
        else ext) extension rules

isRuleApplicable :: DefaultRule -> Set String -> Set String -> Bool
isRuleApplicable rule extension exceptions = 
    let prereqSatisfied = Set.member (prerequisite rule) extension
        justsSatisfied = all (\just -> 
            if just `startsWith` "not "
            then let prop = drop 4 just
                 in not (Set.member prop extension)
            else Set.member just extension) (justifications rule)
        notException = not (Set.member (conclusion rule) exceptions)
    in prereqSatisfied && justsSatisfied && notException

startsWith :: String -> String -> Bool
startsWith str prefix = take (length prefix) str == prefix

query :: String -> NonMonotonicReasoner -> Maybe Bool
query queryStr reasoner = 
    let extension = computeExtension reasoner
    in if Set.member queryStr extension
       then Just True
       else if Set.member ("not " ++ queryStr) extension
            then Just False
            else Nothing

-- 异常处理器操作
addClass :: String -> Maybe String -> ExceptionHandler -> ExceptionHandler
addClass className superclass handler = 
    handler { hierarchy = Map.insert className superclass (hierarchy handler)
            , properties = Map.insert className Set.empty (properties handler)
            , exceptions = Map.insert className Set.empty (exceptions handler)
            }

addProperty :: String -> String -> ExceptionHandler -> ExceptionHandler
addProperty className propertyName handler = 
    case Map.lookup className (properties handler) of
        Just props -> handler { properties = Map.insert className (Set.insert propertyName props) (properties handler) }
        Nothing -> handler

addException :: String -> String -> ExceptionHandler -> ExceptionHandler
addException className propertyName handler = 
    case Map.lookup className (exceptions handler) of
        Just excs -> handler { exceptions = Map.insert className (Set.insert propertyName excs) (exceptions handler) }
        Nothing -> handler

hasProperty :: String -> String -> ExceptionHandler -> Bool
hasProperty className propertyName handler = 
    -- 检查直接异常
    let isException = case Map.lookup className (exceptions handler) of
                        Just excs -> Set.member propertyName excs
                        Nothing -> False
    in if isException
       then False
       else 
           -- 检查直接属性
           let hasDirectProperty = case Map.lookup className (properties handler) of
                                     Just props -> Set.member propertyName props
                                     Nothing -> False
           in if hasDirectProperty
              then True
              else 
                  -- 检查继承
                  case Map.lookup className (hierarchy handler) of
                      Just (Just superclass) -> hasProperty superclass propertyName handler
                      _ -> False

getAllProperties :: String -> ExceptionHandler -> Set String
getAllProperties className handler = 
    let directProperties = Map.findWithDefault Set.empty className (properties handler)
        inheritedProperties = case Map.lookup className (hierarchy handler) of
                                Just (Just superclass) -> getAllProperties superclass handler
                                _ -> Set.empty
        allProperties = Set.union directProperties inheritedProperties
        classExceptions = Map.findWithDefault Set.empty className (exceptions handler)
    in Set.difference allProperties classExceptions

-- 示例使用
main :: IO ()
main = do
    -- 创建默认理论
    let theory = addFact "Bird(tweety)" 
                $ addFact "Bird(penguin)" 
                $ addRule "Bird(x)" ["not cannot_fly(x)"] "can_fly(x)" defaultTheory
    
    -- 创建推理器
    let reasoner = addException "can_fly(penguin)" (nonMonotonicReasoner theory)
    
    -- 推理
    putStrLn $ "Tweety can fly: " ++ show (query "can_fly(tweety)" reasoner)
    putStrLn $ "Penguin can fly: " ++ show (query "can_fly(penguin)" reasoner)
    
    -- 异常处理
    let handler = addClass "Penguin" (Just "Bird") 
                $ addClass "Bird" (Just "Animal") 
                $ addClass "Animal" Nothing exceptionHandler
    
    let handler1 = addProperty "Animal" "breathes" handler
    let handler2 = addProperty "Bird" "flies" handler1
    let handler3 = addProperty "Bird" "lays_eggs" handler2
    let finalHandler = addException "Penguin" "flies" handler3
    
    -- 检查属性
    putStrLn $ "Penguin flies: " ++ show (hasProperty "Penguin" "flies" finalHandler)
    putStrLn $ "Penguin lays eggs: " ++ show (hasProperty "Penguin" "lays_eggs" finalHandler)
    putStrLn $ "Penguin properties: " ++ show (getAllProperties "Penguin" finalHandler)
```

## 总结

非单调逻辑为处理推理中的不确定性、例外情况和知识更新提供了强大的理论工具。通过允许推理结论在添加新信息时被撤销，非单调逻辑能够更准确地模拟人类的常识推理过程。

非单调逻辑的语义理论基于扩展、异常处理和优先语义，提供了严格的数学基础。通过代码实现，我们可以实际应用非单调逻辑来解决各种常识推理和知识表示问题，特别是在人工智能、知识工程和常识推理等领域。

非单调逻辑是经典逻辑的重要扩展，为人工智能和知识表示的发展提供了重要的理论基础，为智能系统的推理能力提供了强有力的支持。 