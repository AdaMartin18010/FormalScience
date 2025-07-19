# 19 人工智能理论 (Artificial Intelligence Theory)

## 模块概述

人工智能理论是研究如何使计算机系统具备智能行为的科学分支，为机器学习、深度学习、自然语言处理等领域提供理论基础。本模块涵盖从符号推理到神经网络的完整理论体系，包括知识表示、推理机制、学习算法和智能系统等核心内容。

## 目录结构

```text
19_Artificial_Intelligence_Theory/
├── README.md                           # 模块总览
├── 19.1_Machine_Learning/              # 机器学习
├── 19.2_Deep_Learning/                 # 深度学习
├── 19.3_Natural_Language_Processing/   # 自然语言处理
├── 19.4_Computer_Vision/               # 计算机视觉
├── 19.5_Knowledge_Representation/      # 知识表示
├── 19.6_Reasoning_Systems/             # 推理系统
├── 19.7_Formal_AI/                     # 形式化人工智能
├── 19.8_AI_Ethics/                     # 人工智能伦理
└── Resources/                          # 资源目录
    ├── Examples/                       # 示例代码
    ├── Exercises/                      # 练习题
    └── References/                     # 参考文献
```

## 理论基础

### 核心概念

**定义 19.1 (人工智能)** 人工智能是使计算机系统能够执行通常需要人类智能的任务的技术。

**定义 19.2 (机器学习)** 机器学习是使计算机系统能够从数据中自动学习和改进的算法和统计模型。

**定义 19.3 (深度学习)** 深度学习是使用多层神经网络进行特征学习和模式识别的机器学习方法。

**定义 19.4 (知识表示)** 知识表示是将人类知识编码为计算机可处理形式的方法。

### 基本模型

**符号AI模型**：

- 基于逻辑和规则的推理
- 符号操作和模式匹配
- 专家系统和知识库

**连接主义模型**：

- 基于神经网络的并行处理
- 分布式表示和权重调整
- 深度学习和神经网络

**行为主义模型**：

- 基于强化学习的行为优化
- 环境交互和奖励机制
- 智能体和多智能体系统

## 形式化实现

### 基础数据结构

```rust
use std::collections::HashMap;
use nalgebra::{DMatrix, DVector};
use serde::{Serialize, Deserialize};

// 神经网络层
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeuralLayer {
    pub weights: DMatrix<f64>,
    pub biases: DVector<f64>,
    pub activation_function: ActivationFunction,
    pub input_size: usize,
    pub output_size: usize,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ActivationFunction {
    Sigmoid,
    Tanh,
    ReLU,
    LeakyReLU,
    Softmax,
    Linear,
}

impl NeuralLayer {
    pub fn new(input_size: usize, output_size: usize, activation: ActivationFunction) -> Self {
        NeuralLayer {
            weights: DMatrix::random(output_size, input_size),
            biases: DVector::zeros(output_size),
            activation_function: activation,
            input_size,
            output_size,
        }
    }

    // 前向传播
    pub fn forward(&self, input: &DVector<f64>) -> DVector<f64> {
        let linear_output = &self.weights * input + &self.biases;
        self.apply_activation(&linear_output)
    }

    // 应用激活函数
    fn apply_activation(&self, input: &DVector<f64>) -> DVector<f64> {
        match self.activation_function {
            ActivationFunction::Sigmoid => {
                input.map(|x| 1.0 / (1.0 + (-x).exp()))
            },
            ActivationFunction::Tanh => {
                input.map(|x| x.tanh())
            },
            ActivationFunction::ReLU => {
                input.map(|x| x.max(0.0))
            },
            ActivationFunction::LeakyReLU => {
                input.map(|x| if x > 0.0 { x } else { 0.01 * x })
            },
            ActivationFunction::Softmax => {
                let max_val = input.max();
                let exp_input = input.map(|x| (x - max_val).exp());
                let sum = exp_input.sum();
                exp_input.map(|x| x / sum)
            },
            ActivationFunction::Linear => {
                input.clone()
            },
        }
    }

    // 计算激活函数导数
    fn activation_derivative(&self, input: &DVector<f64>) -> DVector<f64> {
        match self.activation_function {
            ActivationFunction::Sigmoid => {
                let sigmoid = self.apply_activation(input);
                sigmoid.map(|x| x * (1.0 - x))
            },
            ActivationFunction::Tanh => {
                let tanh = self.apply_activation(input);
                tanh.map(|x| 1.0 - x * x)
            },
            ActivationFunction::ReLU => {
                input.map(|x| if x > 0.0 { 1.0 } else { 0.0 })
            },
            ActivationFunction::LeakyReLU => {
                input.map(|x| if x > 0.0 { 1.0 } else { 0.01 })
            },
            _ => DVector::ones(input.len()),
        }
    }
}

// 神经网络
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeuralNetwork {
    pub layers: Vec<NeuralLayer>,
    pub learning_rate: f64,
}

impl NeuralNetwork {
    pub fn new(learning_rate: f64) -> Self {
        NeuralNetwork {
            layers: vec![],
            learning_rate,
        }
    }

    pub fn add_layer(&mut self, layer: NeuralLayer) {
        self.layers.push(layer);
    }

    // 前向传播
    pub fn forward(&self, input: &DVector<f64>) -> DVector<f64> {
        let mut current_input = input.clone();
        
        for layer in &self.layers {
            current_input = layer.forward(&current_input);
        }
        
        current_input
    }

    // 反向传播
    pub fn backward(&mut self, input: &DVector<f64>, target: &DVector<f64>) -> f64 {
        // 前向传播
        let mut activations = vec![input.clone()];
        let mut layer_inputs = vec![];
        
        for layer in &self.layers {
            let layer_input = activations.last().unwrap().clone();
            layer_inputs.push(layer_input.clone());
            
            let activation = layer.forward(&layer_input);
            activations.push(activation);
        }
        
        // 计算损失
        let output = activations.last().unwrap();
        let loss = self.compute_loss(output, target);
        
        // 反向传播误差
        let mut delta = self.compute_output_delta(output, target);
        
        for (i, layer) in self.layers.iter_mut().enumerate().rev() {
            let layer_input = &layer_inputs[i];
            let activation = &activations[i];
            
            // 计算权重梯度
            let weight_gradient = &delta * layer_input.transpose();
            let bias_gradient = delta.clone();
            
            // 更新权重和偏置
            layer.weights -= &(weight_gradient * self.learning_rate);
            layer.biases -= &(bias_gradient * self.learning_rate);
            
            // 计算下一层的误差
            if i > 0 {
                let activation_derivative = layer.activation_derivative(activation);
                delta = layer.weights.transpose() * &delta;
                delta = delta.component_mul(&activation_derivative);
            }
        }
        
        loss
    }

    // 计算损失
    fn compute_loss(&self, output: &DVector<f64>, target: &DVector<f64>) -> f64 {
        // 均方误差
        let diff = output - target;
        diff.dot(&diff) / output.len() as f64
    }

    // 计算输出层误差
    fn compute_output_delta(&self, output: &DVector<f64>, target: &DVector<f64>) -> DVector<f64> {
        output - target
    }
}

// 知识表示
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KnowledgeBase {
    pub facts: Vec<Fact>,
    pub rules: Vec<Rule>,
    pub entities: HashMap<String, Entity>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Fact {
    pub id: String,
    pub predicate: String,
    pub arguments: Vec<String>,
    pub confidence: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Rule {
    pub id: String,
    pub premises: Vec<Fact>,
    pub conclusion: Fact,
    pub confidence: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Entity {
    pub id: String,
    pub name: String,
    pub attributes: HashMap<String, String>,
    pub relationships: Vec<Relationship>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Relationship {
    pub target: String,
    pub relationship_type: String,
    pub confidence: f64,
}

impl KnowledgeBase {
    pub fn new() -> Self {
        KnowledgeBase {
            facts: vec![],
            rules: vec![],
            entities: HashMap::new(),
        }
    }

    pub fn add_fact(&mut self, fact: Fact) {
        self.facts.push(fact);
    }

    pub fn add_rule(&mut self, rule: Rule) {
        self.rules.push(rule);
    }

    pub fn add_entity(&mut self, entity: Entity) {
        self.entities.insert(entity.id.clone(), entity);
    }

    // 推理
    pub fn reason(&self, query: &Fact) -> Vec<Fact> {
        let mut results = vec![];
        
        // 直接匹配事实
        for fact in &self.facts {
            if self.match_fact(fact, query) {
                results.push(fact.clone());
            }
        }
        
        // 应用规则
        for rule in &self.rules {
            if self.apply_rule(rule, query) {
                results.push(rule.conclusion.clone());
            }
        }
        
        results
    }

    fn match_fact(&self, fact: &Fact, query: &Fact) -> bool {
        fact.predicate == query.predicate && 
        fact.arguments.len() == query.arguments.len() &&
        fact.arguments.iter().zip(&query.arguments)
            .all(|(a, b)| a == b || b == "?")
    }

    fn apply_rule(&self, rule: &Rule, query: &Fact) -> bool {
        // 检查前提是否满足
        let premises_satisfied = rule.premises.iter()
            .all(|premise| self.facts.iter().any(|fact| self.match_fact(fact, premise)));
        
        premises_satisfied && self.match_fact(&rule.conclusion, query)
    }
}

// 强化学习智能体
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReinforcementAgent {
    pub state_size: usize,
    pub action_size: usize,
    pub q_table: HashMap<String, HashMap<String, f64>>,
    pub learning_rate: f64,
    pub discount_factor: f64,
    pub epsilon: f64,
}

impl ReinforcementAgent {
    pub fn new(state_size: usize, action_size: usize) -> Self {
        ReinforcementAgent {
            state_size,
            action_size,
            q_table: HashMap::new(),
            learning_rate: 0.1,
            discount_factor: 0.9,
            epsilon: 0.1,
        }
    }

    // 选择动作
    pub fn select_action(&self, state: &str) -> String {
        if rand::random::<f64>() < self.epsilon {
            // 探索：随机选择动作
            format!("action_{}", rand::random::<usize>() % self.action_size)
        } else {
            // 利用：选择Q值最大的动作
            if let Some(actions) = self.q_table.get(state) {
                actions.iter()
                    .max_by(|(_, q1), (_, q2)| q1.partial_cmp(q2).unwrap())
                    .map(|(action, _)| action.clone())
                    .unwrap_or_else(|| format!("action_0"))
            } else {
                format!("action_0")
            }
        }
    }

    // 更新Q值
    pub fn update_q_value(&mut self, state: &str, action: &str, reward: f64, next_state: &str) {
        let current_q = self.q_table
            .entry(state.to_string())
            .or_insert_with(HashMap::new)
            .entry(action.to_string())
            .or_insert(0.0);
        
        let next_max_q = self.q_table
            .get(next_state)
            .map(|actions| actions.values().fold(0.0, |max, &q| max.max(q)))
            .unwrap_or(0.0);
        
        *current_q = *current_q + self.learning_rate * 
            (reward + self.discount_factor * next_max_q - *current_q);
    }
}

// 自然语言处理
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NLPProcessor {
    pub vocabulary: HashMap<String, usize>,
    pub word_embeddings: HashMap<String, DVector<f64>>,
    pub language_model: Option<NeuralNetwork>,
}

impl NLPProcessor {
    pub fn new() -> Self {
        NLPProcessor {
            vocabulary: HashMap::new(),
            word_embeddings: HashMap::new(),
            language_model: None,
        }
    }

    // 分词
    pub fn tokenize(&self, text: &str) -> Vec<String> {
        text.split_whitespace()
            .map(|word| word.to_lowercase())
            .collect()
    }

    // 构建词汇表
    pub fn build_vocabulary(&mut self, texts: &[String]) {
        let mut word_counts = HashMap::new();
        
        for text in texts {
            let tokens = self.tokenize(text);
            for token in tokens {
                *word_counts.entry(token).or_insert(0) += 1;
            }
        }
        
        for (word, _) in word_counts.iter().take(1000) {
            self.vocabulary.insert(word.clone(), self.vocabulary.len());
        }
    }

    // 文本向量化
    pub fn vectorize(&self, text: &str) -> DVector<f64> {
        let tokens = self.tokenize(text);
        let mut vector = DVector::zeros(self.vocabulary.len());
        
        for token in tokens {
            if let Some(&index) = self.vocabulary.get(&token) {
                vector[index] += 1.0;
            }
        }
        
        vector
    }

    // 计算文本相似度
    pub fn similarity(&self, text1: &str, text2: &str) -> f64 {
        let vec1 = self.vectorize(text1);
        let vec2 = self.vectorize(text2);
        
        let dot_product = vec1.dot(&vec2);
        let norm1 = vec1.norm();
        let norm2 = vec2.norm();
        
        if norm1 > 0.0 && norm2 > 0.0 {
            dot_product / (norm1 * norm2)
        } else {
            0.0
        }
    }
}
```

### 机器学习算法

```rust
// 线性回归
pub struct LinearRegression {
    pub weights: DVector<f64>,
    pub bias: f64,
    pub learning_rate: f64,
}

impl LinearRegression {
    pub fn new(feature_count: usize, learning_rate: f64) -> Self {
        LinearRegression {
            weights: DVector::zeros(feature_count),
            bias: 0.0,
            learning_rate,
        }
    }

    pub fn fit(&mut self, X: &DMatrix<f64>, y: &DVector<f64>, epochs: usize) {
        for _ in 0..epochs {
            for i in 0..X.nrows() {
                let features = X.row(i);
                let target = y[i];
                
                // 前向传播
                let prediction = self.predict_single(&features);
                
                // 计算梯度
                let error = prediction - target;
                
                // 更新权重
                for j in 0..self.weights.len() {
                    self.weights[j] -= self.learning_rate * error * features[j];
                }
                self.bias -= self.learning_rate * error;
            }
        }
    }

    pub fn predict_single(&self, features: &nalgebra::RowVector<f64>) -> f64 {
        features.dot(&self.weights) + self.bias
    }

    pub fn predict(&self, X: &DMatrix<f64>) -> DVector<f64> {
        let mut predictions = DVector::zeros(X.nrows());
        
        for i in 0..X.nrows() {
            let features = X.row(i);
            predictions[i] = self.predict_single(&features);
        }
        
        predictions
    }
}

// 决策树
#[derive(Debug, Clone)]
pub struct DecisionTree {
    pub root: Option<TreeNode>,
    pub max_depth: usize,
}

#[derive(Debug, Clone)]
pub struct TreeNode {
    pub feature_index: Option<usize>,
    pub threshold: Option<f64>,
    pub value: Option<f64>,
    pub left: Option<Box<TreeNode>>,
    pub right: Option<Box<TreeNode>>,
}

impl DecisionTree {
    pub fn new(max_depth: usize) -> Self {
        DecisionTree {
            root: None,
            max_depth,
        }
    }

    pub fn fit(&mut self, X: &DMatrix<f64>, y: &DVector<f64>) {
        self.root = Some(self.build_tree(X, y, 0));
    }

    fn build_tree(&self, X: &DMatrix<f64>, y: &DVector<f64>, depth: usize) -> TreeNode {
        // 检查停止条件
        if depth >= self.max_depth || self.is_pure(y) {
            return TreeNode {
                feature_index: None,
                threshold: None,
                value: Some(self.mean(y)),
                left: None,
                right: None,
            };
        }
        
        // 寻找最佳分割
        if let Some((feature_index, threshold)) = self.find_best_split(X, y) {
            let (left_indices, right_indices) = self.split_data(X, feature_index, threshold);
            
            let left_X = self.select_rows(X, &left_indices);
            let left_y = self.select_elements(y, &left_indices);
            let right_X = self.select_rows(X, &right_indices);
            let right_y = self.select_elements(y, &right_indices);
            
            TreeNode {
                feature_index: Some(feature_index),
                threshold: Some(threshold),
                value: None,
                left: Some(Box::new(self.build_tree(&left_X, &left_y, depth + 1))),
                right: Some(Box::new(self.build_tree(&right_X, &right_y, depth + 1))),
            }
        } else {
            TreeNode {
                feature_index: None,
                threshold: None,
                value: Some(self.mean(y)),
                left: None,
                right: None,
            }
        }
    }

    fn is_pure(&self, y: &DVector<f64>) -> bool {
        if y.len() == 0 {
            return true;
        }
        let first_value = y[0];
        y.iter().all(|&value| value == first_value)
    }

    fn mean(&self, y: &DVector<f64>) -> f64 {
        y.sum() / y.len() as f64
    }

    fn find_best_split(&self, X: &DMatrix<f64>, y: &DVector<f64>) -> Option<(usize, f64)> {
        let mut best_gain = 0.0;
        let mut best_feature = None;
        let mut best_threshold = 0.0;
        
        for feature in 0..X.ncols() {
            let mut values: Vec<f64> = X.column(feature).iter().cloned().collect();
            values.sort_by(|a, b| a.partial_cmp(b).unwrap());
            
            for i in 0..values.len() - 1 {
                let threshold = (values[i] + values[i + 1]) / 2.0;
                let gain = self.information_gain(X, y, feature, threshold);
                
                if gain > best_gain {
                    best_gain = gain;
                    best_feature = Some(feature);
                    best_threshold = threshold;
                }
            }
        }
        
        best_feature.map(|feature| (feature, best_threshold))
    }

    fn information_gain(&self, X: &DMatrix<f64>, y: &DVector<f64>, feature: usize, threshold: f64) -> f64 {
        let parent_entropy = self.entropy(y);
        
        let (left_indices, right_indices) = self.split_data(X, feature, threshold);
        let left_y = self.select_elements(y, &left_indices);
        let right_y = self.select_elements(y, &right_indices);
        
        let left_entropy = self.entropy(&left_y);
        let right_entropy = self.entropy(&right_y);
        
        let left_weight = left_y.len() as f64 / y.len() as f64;
        let right_weight = right_y.len() as f64 / y.len() as f64;
        
        parent_entropy - (left_weight * left_entropy + right_weight * right_entropy)
    }

    fn entropy(&self, y: &DVector<f64>) -> f64 {
        let mut counts = HashMap::new();
        for &value in y.iter() {
            *counts.entry(value as i64).or_insert(0) += 1;
        }
        
        let mut entropy = 0.0;
        let total = y.len() as f64;
        
        for count in counts.values() {
            let probability = *count as f64 / total;
            if probability > 0.0 {
                entropy -= probability * probability.log2();
            }
        }
        
        entropy
    }

    fn split_data(&self, X: &DMatrix<f64>, feature: usize, threshold: f64) -> (Vec<usize>, Vec<usize>) {
        let mut left_indices = vec![];
        let mut right_indices = vec![];
        
        for i in 0..X.nrows() {
            if X[(i, feature)] <= threshold {
                left_indices.push(i);
            } else {
                right_indices.push(i);
            }
        }
        
        (left_indices, right_indices)
    }

    fn select_rows(&self, X: &DMatrix<f64>, indices: &[usize]) -> DMatrix<f64> {
        let mut result = DMatrix::zeros(indices.len(), X.ncols());
        for (i, &index) in indices.iter().enumerate() {
            for j in 0..X.ncols() {
                result[(i, j)] = X[(index, j)];
            }
        }
        result
    }

    fn select_elements(&self, y: &DVector<f64>, indices: &[usize]) -> DVector<f64> {
        let mut result = DVector::zeros(indices.len());
        for (i, &index) in indices.iter().enumerate() {
            result[i] = y[index];
        }
        result
    }

    pub fn predict(&self, X: &DMatrix<f64>) -> DVector<f64> {
        let mut predictions = DVector::zeros(X.nrows());
        
        for i in 0..X.nrows() {
            let features = X.row(i);
            predictions[i] = self.predict_single(&features);
        }
        
        predictions
    }

    fn predict_single(&self, features: &nalgebra::RowVector<f64>) -> f64 {
        if let Some(ref root) = self.root {
            self.predict_node(root, features)
        } else {
            0.0
        }
    }

    fn predict_node(&self, node: &TreeNode, features: &nalgebra::RowVector<f64>) -> f64 {
        if let Some(value) = node.value {
            return value;
        }
        
        if let (Some(feature_index), Some(threshold)) = (node.feature_index, node.threshold) {
            if features[feature_index] <= threshold {
                if let Some(ref left) = node.left {
                    self.predict_node(left, features)
                } else {
                    0.0
                }
            } else {
                if let Some(ref right) = node.right {
                    self.predict_node(right, features)
                } else {
                    0.0
                }
            }
        } else {
            0.0
        }
    }
}
```

## 应用示例

### 神经网络示例

```rust
fn neural_network_example() {
    // 创建神经网络
    let mut network = NeuralNetwork::new(0.01);
    
    // 添加层
    network.add_layer(NeuralLayer::new(2, 4, ActivationFunction::ReLU));
    network.add_layer(NeuralLayer::new(4, 3, ActivationFunction::ReLU));
    network.add_layer(NeuralLayer::new(3, 1, ActivationFunction::Linear));
    
    // 训练数据
    let mut X = DMatrix::zeros(100, 2);
    let mut y = DVector::zeros(100);
    
    for i in 0..100 {
        X[(i, 0)] = rand::random::<f64>() * 2.0 - 1.0;
        X[(i, 1)] = rand::random::<f64>() * 2.0 - 1.0;
        y[i] = X[(i, 0)] + X[(i, 1)]; // 简单的加法函数
    }
    
    // 训练网络
    for epoch in 0..1000 {
        let mut total_loss = 0.0;
        
        for i in 0..X.nrows() {
            let input = X.row(i).transpose();
            let target = DVector::from_vec(vec![y[i]]);
            
            let loss = network.backward(&input, &target);
            total_loss += loss;
        }
        
        if epoch % 100 == 0 {
            println!("Epoch {}, Average Loss: {:.6}", epoch, total_loss / X.nrows() as f64);
        }
    }
    
    // 测试网络
    let test_input = DVector::from_vec(vec![0.5, 0.3]);
    let prediction = network.forward(&test_input);
    println!("预测结果: {:.3} + {:.3} = {:.3}", test_input[0], test_input[1], prediction[0]);
}
```

### 知识推理示例

```rust
fn knowledge_reasoning_example() {
    // 创建知识库
    let mut kb = KnowledgeBase::new();
    
    // 添加事实
    kb.add_fact(Fact {
        id: "fact1".to_string(),
        predicate: "is_a".to_string(),
        arguments: vec!["Socrates".to_string(), "human".to_string()],
        confidence: 1.0,
    });
    
    kb.add_fact(Fact {
        id: "fact2".to_string(),
        predicate: "is_a".to_string(),
        arguments: vec!["human".to_string(), "mortal".to_string()],
        confidence: 1.0,
    });
    
    // 添加规则
    kb.add_rule(Rule {
        id: "rule1".to_string(),
        premises: vec![
            Fact {
                id: "premise1".to_string(),
                predicate: "is_a".to_string(),
                arguments: vec!["?x".to_string(), "human".to_string()],
                confidence: 1.0,
            }
        ],
        conclusion: Fact {
            id: "conclusion1".to_string(),
            predicate: "is_a".to_string(),
            arguments: vec!["?x".to_string(), "mortal".to_string()],
            confidence: 1.0,
        },
        confidence: 1.0,
    });
    
    // 进行推理
    let query = Fact {
        id: "query1".to_string(),
        predicate: "is_a".to_string(),
        arguments: vec!["Socrates".to_string(), "mortal".to_string()],
        confidence: 1.0,
    };
    
    let results = kb.reason(&query);
    println!("推理结果:");
    for result in results {
        println!("- {}: {:?}", result.predicate, result.arguments);
    }
}
```

### 强化学习示例

```rust
fn reinforcement_learning_example() {
    // 创建智能体
    let mut agent = ReinforcementAgent::new(4, 2);
    
    // 简单的网格世界环境
    let mut state = "start".to_string();
    let mut total_reward = 0.0;
    
    for episode in 0..100 {
        let mut episode_reward = 0.0;
        let mut steps = 0;
        
        while steps < 100 {
            // 选择动作
            let action = agent.select_action(&state);
            
            // 模拟环境响应
            let (next_state, reward) = simulate_environment(&state, &action);
            
            // 更新Q值
            agent.update_q_value(&state, &action, reward, &next_state);
            
            episode_reward += reward;
            state = next_state;
            steps += 1;
            
            if state == "goal" {
                break;
            }
        }
        
        total_reward += episode_reward;
        
        if episode % 10 == 0 {
            println!("Episode {}, Average Reward: {:.2}", episode, total_reward / (episode + 1) as f64);
        }
    }
}

fn simulate_environment(state: &str, action: &str) -> (String, f64) {
    // 简化的环境模拟
    match (state, action) {
        ("start", "action_0") => ("middle".to_string(), 0.0),
        ("start", "action_1") => ("goal".to_string(), 1.0),
        ("middle", "action_0") => ("goal".to_string(), 1.0),
        ("middle", "action_1") => ("start".to_string(), 0.0),
        _ => (state.to_string(), 0.0),
    }
}
```

## 理论扩展

### 深度学习理论

**定理 19.1 (通用近似定理)** 具有单个隐藏层的前馈神经网络可以近似任何连续函数。

**定理 19.2 (深度优势)** 深度网络可以表示某些函数，而浅层网络需要指数级更多的参数。

### 强化学习理论

**定理 19.3 (策略梯度定理)** 策略梯度的期望值等于策略性能的梯度。

**定理 19.4 (贝尔曼方程)** 最优价值函数满足贝尔曼最优性方程。

## 批判性分析

### 理论优势

1. **通用性**：可以处理各种类型的问题
2. **自适应性**：能够从数据中学习
3. **可扩展性**：可以处理大规模数据

### 理论局限性

1. **黑盒问题**：决策过程难以解释
2. **数据依赖**：需要大量高质量数据
3. **计算复杂性**：某些算法计算成本高

### 应用挑战

1. **偏见问题**：可能继承训练数据的偏见
2. **鲁棒性**：对输入扰动敏感
3. **安全性**：可能被恶意攻击

## 相关链接

- [02.05 代数理论](../../02_Mathematical_Foundations/02.05_Algebra/README.md)
- [02.08 分析理论](../../02_Mathematical_Foundations/02.08_Analysis/README.md)
- [17.01 数据科学理论](../../17_Data_Science_Theory/README.md)

---

**最后更新**：2025-01-17  
**模块状态**：✅ 完成
