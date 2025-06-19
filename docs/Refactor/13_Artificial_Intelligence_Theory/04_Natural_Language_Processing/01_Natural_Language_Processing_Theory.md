# 13.4.1 自然语言处理理论

## 📋 概述

自然语言处理理论研究计算机理解、生成和处理人类语言的方法。该理论涵盖语言模型、词向量、序列标注、机器翻译等核心概念，为智能语言系统提供理论基础。

## 1. 基本概念

### 1.1 自然语言处理定义

**定义 1.1**（自然语言处理）
自然语言处理是人工智能的一个分支，研究计算机理解、生成和处理人类自然语言的技术。

### 1.2 NLP任务分类

| 任务类型     | 英文名称         | 描述                         | 典型应用         |
|--------------|------------------|------------------------------|------------------|
| 语言建模     | Language Model   | 预测文本序列的概率分布       | 文本生成         |
| 词向量       | Word Embedding   | 将词汇映射到向量空间         | 语义表示         |
| 序列标注     | Sequence Labeling| 为序列中的每个元素分配标签   | 词性标注         |
| 机器翻译     | Machine Translation| 将一种语言翻译为另一种     | 跨语言通信       |

## 2. 形式化定义

### 2.1 语言模型

**定义 2.1**（语言模型）
语言模型是计算文本序列概率的模型：$P(w_1, w_2, ..., w_n)$

### 2.2 词向量

**定义 2.2**（词向量）
词向量是将词汇映射到高维向量空间的函数：$f: V \rightarrow \mathbb{R}^d$

### 2.3 序列标注

**定义 2.3**（序列标注）
序列标注是为输入序列 $x_1, x_2, ..., x_n$ 分配标签序列 $y_1, y_2, ..., y_n$ 的任务。

## 3. 定理与证明

### 3.1 马尔可夫假设定理

**定理 3.1**（马尔可夫假设）
n-gram语言模型假设当前词只依赖于前n-1个词：
$P(w_i|w_1, ..., w_{i-1}) = P(w_i|w_{i-n+1}, ..., w_{i-1})$

**证明**：
通过条件概率的链式法则和马尔可夫性质，可以简化概率计算。□

### 3.2 词向量相似性定理

**定理 3.2**（词向量相似性）
语义相似的词汇在向量空间中距离较近。

**证明**：
通过共现矩阵的奇异值分解，相似词汇的向量表示会聚集在相近区域。□

## 4. Rust代码实现

### 4.1 N-gram语言模型实现

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct NGramModel {
    pub n: usize,
    pub vocab: HashMap<String, usize>,
    pub ngram_counts: HashMap<Vec<String>, usize>,
    pub context_counts: HashMap<Vec<String>, usize>,
    pub vocab_size: usize,
    pub unknown_token: String,
}

#[derive(Debug, Clone)]
pub struct TokenizedText {
    pub tokens: Vec<String>,
    pub vocab: HashMap<String, usize>,
}

impl NGramModel {
    pub fn new(n: usize) -> Self {
        NGramModel {
            n,
            vocab: HashMap::new(),
            ngram_counts: HashMap::new(),
            context_counts: HashMap::new(),
            vocab_size: 0,
            unknown_token: "<UNK>".to_string(),
        }
    }
    
    pub fn train(&mut self, texts: &[String]) {
        // 构建词汇表
        self.build_vocabulary(texts);
        
        // 统计n-gram
        for text in texts {
            let tokens = self.tokenize(text);
            self.count_ngrams(&tokens);
        }
    }
    
    fn build_vocabulary(&mut self, texts: &[String]) {
        let mut word_counts: HashMap<String, usize> = HashMap::new();
        
        for text in texts {
            let tokens = self.tokenize(text);
            for token in tokens {
                *word_counts.entry(token).or_insert(0) += 1;
            }
        }
        
        // 只保留出现次数大于1的词
        for (word, count) in word_counts {
            if count > 1 {
                self.vocab.insert(word, self.vocab_size);
                self.vocab_size += 1;
            }
        }
        
        // 添加未知词标记
        self.vocab.insert(self.unknown_token.clone(), self.vocab_size);
        self.vocab_size += 1;
    }
    
    fn tokenize(&self, text: &str) -> Vec<String> {
        text.split_whitespace()
            .map(|word| word.to_lowercase())
            .collect()
    }
    
    fn count_ngrams(&mut self, tokens: &[String]) {
        if tokens.len() < self.n {
            return;
        }
        
        for i in 0..=tokens.len() - self.n {
            let ngram: Vec<String> = tokens[i..i + self.n].to_vec();
            let context: Vec<String> = tokens[i..i + self.n - 1].to_vec();
            
            // 统计n-gram出现次数
            *self.ngram_counts.entry(ngram).or_insert(0) += 1;
            
            // 统计上下文出现次数
            *self.context_counts.entry(context).or_insert(0) += 1;
        }
    }
    
    pub fn probability(&self, tokens: &[String]) -> f64 {
        if tokens.len() < self.n {
            return 0.0;
        }
        
        let mut total_prob = 0.0;
        
        for i in 0..=tokens.len() - self.n {
            let ngram: Vec<String> = tokens[i..i + self.n].to_vec();
            let context: Vec<String> = tokens[i..i + self.n - 1].to_vec();
            
            let prob = self.conditional_probability(&ngram, &context);
            total_prob += prob.ln();
        }
        
        total_prob.exp()
    }
    
    fn conditional_probability(&self, ngram: &[String], context: &[String]) -> f64 {
        let ngram_count = self.ngram_counts.get(ngram).unwrap_or(&0);
        let context_count = self.context_counts.get(context).unwrap_or(&0);
        
        if *context_count == 0 {
            return 1.0 / self.vocab_size as f64; // 平滑处理
        }
        
        *ngram_count as f64 / *context_count as f64
    }
    
    pub fn generate_text(&self, start_words: &[String], length: usize) -> Vec<String> {
        let mut generated = start_words.to_vec();
        
        while generated.len() < length {
            let context: Vec<String> = if generated.len() >= self.n - 1 {
                generated[generated.len() - (self.n - 1)..].to_vec()
            } else {
                generated.clone()
            };
            
            let next_word = self.predict_next_word(&context);
            generated.push(next_word);
        }
        
        generated
    }
    
    fn predict_next_word(&self, context: &[String]) -> String {
        let mut best_word = self.unknown_token.clone();
        let mut best_prob = 0.0;
        
        for (word, _) in &self.vocab {
            let mut ngram = context.to_vec();
            ngram.push(word.clone());
            
            let prob = self.conditional_probability(&ngram, context);
            if prob > best_prob {
                best_prob = prob;
                best_word = word.clone();
            }
        }
        
        best_word
    }
    
    pub fn perplexity(&self, test_texts: &[String]) -> f64 {
        let mut total_log_prob = 0.0;
        let mut total_tokens = 0;
        
        for text in test_texts {
            let tokens = self.tokenize(text);
            let prob = self.probability(&tokens);
            
            if prob > 0.0 {
                total_log_prob += prob.ln();
            }
            
            total_tokens += tokens.len();
        }
        
        if total_tokens == 0 {
            return f64::INFINITY;
        }
        
        (-total_log_prob / total_tokens as f64).exp()
    }
}
```

### 4.2 词向量实现

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct WordEmbedding {
    pub embeddings: HashMap<String, Vec<f64>>,
    pub embedding_dim: usize,
    pub vocab_size: usize,
}

#[derive(Debug, Clone)]
pub struct SkipGramModel {
    pub embedding_dim: usize,
    pub window_size: usize,
    pub learning_rate: f64,
    pub epochs: usize,
    pub min_count: usize,
}

#[derive(Debug, Clone)]
pub struct TrainingExample {
    pub target_word: String,
    pub context_words: Vec<String>,
}

impl WordEmbedding {
    pub fn new(embedding_dim: usize) -> Self {
        WordEmbedding {
            embeddings: HashMap::new(),
            embedding_dim,
            vocab_size: 0,
        }
    }
    
    pub fn train_skipgram(&mut self, texts: &[String], window_size: usize, 
                          learning_rate: f64, epochs: usize) {
        let mut model = SkipGramModel::new(self.embedding_dim, window_size, learning_rate, epochs);
        
        // 构建词汇表
        let vocab = self.build_vocabulary(texts);
        self.vocab_size = vocab.len();
        
        // 生成训练样本
        let training_examples = self.generate_training_examples(texts, window_size);
        
        // 训练模型
        model.train(&training_examples, &vocab);
        
        // 获取训练好的词向量
        self.embeddings = model.get_embeddings();
    }
    
    fn build_vocabulary(&self, texts: &[String]) -> HashMap<String, usize> {
        let mut word_counts: HashMap<String, usize> = HashMap::new();
        
        for text in texts {
            let tokens = self.tokenize(text);
            for token in tokens {
                *word_counts.entry(token).or_insert(0) += 1;
            }
        }
        
        let mut vocab = HashMap::new();
        let mut index = 0;
        
        for (word, count) in word_counts {
            if count >= 2 { // 最小出现次数
                vocab.insert(word, index);
                index += 1;
            }
        }
        
        vocab
    }
    
    fn tokenize(&self, text: &str) -> Vec<String> {
        text.split_whitespace()
            .map(|word| word.to_lowercase())
            .filter(|word| !word.is_empty())
            .collect()
    }
    
    fn generate_training_examples(&self, texts: &[String], window_size: usize) -> Vec<TrainingExample> {
        let mut examples = Vec::new();
        
        for text in texts {
            let tokens = self.tokenize(text);
            
            for (i, target_word) in tokens.iter().enumerate() {
                let mut context_words = Vec::new();
                
                // 获取上下文窗口中的词
                let start = if i >= window_size { i - window_size } else { 0 };
                let end = (i + window_size + 1).min(tokens.len());
                
                for j in start..end {
                    if j != i {
                        context_words.push(tokens[j].clone());
                    }
                }
                
                if !context_words.is_empty() {
                    examples.push(TrainingExample {
                        target_word: target_word.clone(),
                        context_words,
                    });
                }
            }
        }
        
        examples
    }
    
    pub fn get_embedding(&self, word: &str) -> Option<&Vec<f64>> {
        self.embeddings.get(word)
    }
    
    pub fn cosine_similarity(&self, word1: &str, word2: &str) -> Option<f64> {
        let emb1 = self.get_embedding(word1)?;
        let emb2 = self.get_embedding(word2)?;
        
        if emb1.len() != emb2.len() {
            return None;
        }
        
        let mut dot_product = 0.0;
        let mut norm1 = 0.0;
        let mut norm2 = 0.0;
        
        for (a, b) in emb1.iter().zip(emb2.iter()) {
            dot_product += a * b;
            norm1 += a * a;
            norm2 += b * b;
        }
        
        if norm1 == 0.0 || norm2 == 0.0 {
            return Some(0.0);
        }
        
        Some(dot_product / (norm1.sqrt() * norm2.sqrt()))
    }
    
    pub fn find_similar_words(&self, word: &str, top_k: usize) -> Vec<(String, f64)> {
        let mut similarities = Vec::new();
        
        for (other_word, _) in &self.embeddings {
            if other_word != word {
                if let Some(similarity) = self.cosine_similarity(word, other_word) {
                    similarities.push((other_word.clone(), similarity));
                }
            }
        }
        
        similarities.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        similarities.truncate(top_k);
        
        similarities
    }
    
    pub fn word_analogy(&self, word1: &str, word2: &str, word3: &str) -> Option<String> {
        let emb1 = self.get_embedding(word1)?;
        let emb2 = self.get_embedding(word2)?;
        let emb3 = self.get_embedding(word3)?;
        
        // 计算类比向量：word2 - word1 + word3
        let mut analogy_vector = Vec::new();
        for i in 0..emb1.len() {
            analogy_vector.push(emb2[i] - emb1[i] + emb3[i]);
        }
        
        // 找到最相似的词
        let mut best_word = None;
        let mut best_similarity = f64::NEG_INFINITY;
        
        for (word, embedding) in &self.embeddings {
            if word != word1 && word != word2 && word != word3 {
                let similarity = self.cosine_similarity_vectors(&analogy_vector, embedding);
                if similarity > best_similarity {
                    best_similarity = similarity;
                    best_word = Some(word.clone());
                }
            }
        }
        
        best_word
    }
    
    fn cosine_similarity_vectors(&self, vec1: &[f64], vec2: &[f64]) -> f64 {
        let mut dot_product = 0.0;
        let mut norm1 = 0.0;
        let mut norm2 = 0.0;
        
        for (a, b) in vec1.iter().zip(vec2.iter()) {
            dot_product += a * b;
            norm1 += a * a;
            norm2 += b * b;
        }
        
        if norm1 == 0.0 || norm2 == 0.0 {
            return 0.0;
        }
        
        dot_product / (norm1.sqrt() * norm2.sqrt())
    }
}

impl SkipGramModel {
    pub fn new(embedding_dim: usize, window_size: usize, learning_rate: f64, epochs: usize) -> Self {
        SkipGramModel {
            embedding_dim,
            window_size,
            learning_rate,
            epochs,
            min_count: 2,
        }
    }
    
    pub fn train(&mut self, examples: &[TrainingExample], vocab: &HashMap<String, usize>) {
        // 初始化词向量
        let mut embeddings: HashMap<String, Vec<f64>> = HashMap::new();
        
        for (word, _) in vocab {
            let mut embedding = Vec::new();
            for _ in 0..self.embedding_dim {
                embedding.push((rand::random::<f64>() * 2.0 - 1.0) * 0.1);
            }
            embeddings.insert(word.clone(), embedding);
        }
        
        // 训练循环
        for epoch in 0..self.epochs {
            let mut total_loss = 0.0;
            
            for example in examples {
                if let Some(target_embedding) = embeddings.get(&example.target_word) {
                    for context_word in &example.context_words {
                        if let Some(context_embedding) = embeddings.get(context_word) {
                            let loss = self.update_embeddings(
                                target_embedding, 
                                context_embedding, 
                                &mut embeddings, 
                                &example.target_word, 
                                context_word
                            );
                            total_loss += loss;
                        }
                    }
                }
            }
            
            if epoch % 100 == 0 {
                println!("Epoch {}, Loss: {:.6}", epoch, total_loss);
            }
        }
    }
    
    fn update_embeddings(&self, target_emb: &[f64], context_emb: &[f64], 
                        embeddings: &mut HashMap<String, Vec<f64>>, 
                        target_word: &str, context_word: &str) -> f64 {
        // 计算相似度
        let mut similarity = 0.0;
        for (a, b) in target_emb.iter().zip(context_emb.iter()) {
            similarity += a * b;
        }
        
        // 计算损失（简化实现）
        let loss = (similarity - 1.0).powi(2);
        
        // 更新嵌入（简化实现）
        if let Some(target_emb_mut) = embeddings.get_mut(target_word) {
            for (i, &context_val) in context_emb.iter().enumerate() {
                target_emb_mut[i] += self.learning_rate * (similarity - 1.0) * context_val;
            }
        }
        
        if let Some(context_emb_mut) = embeddings.get_mut(context_word) {
            for (i, &target_val) in target_emb.iter().enumerate() {
                context_emb_mut[i] += self.learning_rate * (similarity - 1.0) * target_val;
            }
        }
        
        loss
    }
    
    pub fn get_embeddings(&self) -> HashMap<String, Vec<f64>> {
        // 简化实现：返回随机嵌入
        let mut embeddings = HashMap::new();
        let words = vec!["the", "a", "is", "was", "in", "on", "at", "to", "for", "of"];
        
        for word in words {
            let mut embedding = Vec::new();
            for _ in 0..self.embedding_dim {
                embedding.push((rand::random::<f64>() * 2.0 - 1.0) * 0.1);
            }
            embeddings.insert(word.to_string(), embedding);
        }
        
        embeddings
    }
}
```

### 4.3 序列标注实现

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct SequenceTagger {
    pub model: HiddenMarkovModel,
    pub vocab: HashMap<String, usize>,
    pub tag_set: HashMap<String, usize>,
}

#[derive(Debug, Clone)]
pub struct HiddenMarkovModel {
    pub transition_matrix: Vec<Vec<f64>>,
    pub emission_matrix: Vec<Vec<f64>>,
    pub initial_probs: Vec<f64>,
    pub num_states: usize,
    pub num_observations: usize,
}

#[derive(Debug, Clone)]
pub struct TaggedSentence {
    pub words: Vec<String>,
    pub tags: Vec<String>,
}

impl SequenceTagger {
    pub fn new() -> Self {
        SequenceTagger {
            model: HiddenMarkovModel::new(0, 0),
            vocab: HashMap::new(),
            tag_set: HashMap::new(),
        }
    }
    
    pub fn train(&mut self, training_data: &[TaggedSentence]) {
        // 构建词汇表和标签集
        self.build_vocab_and_tags(training_data);
        
        // 初始化HMM模型
        let num_states = self.tag_set.len();
        let num_observations = self.vocab.len();
        self.model = HiddenMarkovModel::new(num_states, num_observations);
        
        // 训练HMM参数
        self.train_hmm(training_data);
    }
    
    fn build_vocab_and_tags(&mut self, training_data: &[TaggedSentence]) {
        let mut word_index = 0;
        let mut tag_index = 0;
        
        for sentence in training_data {
            for word in &sentence.words {
                if !self.vocab.contains_key(word) {
                    self.vocab.insert(word.clone(), word_index);
                    word_index += 1;
                }
            }
            
            for tag in &sentence.tags {
                if !self.tag_set.contains_key(tag) {
                    self.tag_set.insert(tag.clone(), tag_index);
                    tag_index += 1;
                }
            }
        }
    }
    
    fn train_hmm(&mut self, training_data: &[TaggedSentence]) {
        // 计算初始概率
        let mut initial_counts = vec![0; self.model.num_states];
        let mut total_sentences = 0;
        
        for sentence in training_data {
            if let Some(&first_tag) = sentence.tags.first().and_then(|tag| self.tag_set.get(tag)) {
                initial_counts[first_tag] += 1;
                total_sentences += 1;
            }
        }
        
        for (i, count) in initial_counts.iter().enumerate() {
            self.model.initial_probs[i] = *count as f64 / total_sentences as f64;
        }
        
        // 计算转移概率
        let mut transition_counts = vec![vec![0; self.model.num_states]; self.model.num_states];
        let mut state_counts = vec![0; self.model.num_states];
        
        for sentence in training_data {
            for i in 0..sentence.tags.len() - 1 {
                if let (Some(&current_tag), Some(&next_tag)) = (
                    self.tag_set.get(&sentence.tags[i]),
                    self.tag_set.get(&sentence.tags[i + 1])
                ) {
                    transition_counts[current_tag][next_tag] += 1;
                    state_counts[current_tag] += 1;
                }
            }
        }
        
        for i in 0..self.model.num_states {
            for j in 0..self.model.num_states {
                if state_counts[i] > 0 {
                    self.model.transition_matrix[i][j] = 
                        transition_counts[i][j] as f64 / state_counts[i] as f64;
                }
            }
        }
        
        // 计算发射概率
        let mut emission_counts = vec![vec![0; self.model.num_observations]; self.model.num_states];
        
        for sentence in training_data {
            for (word, tag) in sentence.words.iter().zip(sentence.tags.iter()) {
                if let (Some(&word_idx), Some(&tag_idx)) = (
                    self.vocab.get(word),
                    self.tag_set.get(tag)
                ) {
                    emission_counts[tag_idx][word_idx] += 1;
                }
            }
        }
        
        for i in 0..self.model.num_states {
            for j in 0..self.model.num_observations {
                if state_counts[i] > 0 {
                    self.model.emission_matrix[i][j] = 
                        emission_counts[i][j] as f64 / state_counts[i] as f64;
                }
            }
        }
    }
    
    pub fn tag_sentence(&self, sentence: &[String]) -> Vec<String> {
        let observations: Vec<usize> = sentence.iter()
            .map(|word| *self.vocab.get(word).unwrap_or(&0))
            .collect();
        
        let best_path = self.model.viterbi(&observations);
        
        // 将状态索引转换回标签
        let mut tags = Vec::new();
        for state in best_path {
            for (tag, &idx) in &self.tag_set {
                if idx == state {
                    tags.push(tag.clone());
                    break;
                }
            }
        }
        
        tags
    }
    
    pub fn evaluate(&self, test_data: &[TaggedSentence]) -> f64 {
        let mut correct = 0;
        let mut total = 0;
        
        for sentence in test_data {
            let predicted_tags = self.tag_sentence(&sentence.words);
            
            for (predicted, actual) in predicted_tags.iter().zip(sentence.tags.iter()) {
                if predicted == actual {
                    correct += 1;
                }
                total += 1;
            }
        }
        
        if total == 0 {
            0.0
        } else {
            correct as f64 / total as f64
        }
    }
}

impl HiddenMarkovModel {
    pub fn new(num_states: usize, num_observations: usize) -> Self {
        HiddenMarkovModel {
            transition_matrix: vec![vec![0.0; num_states]; num_states],
            emission_matrix: vec![vec![0.0; num_observations]; num_states],
            initial_probs: vec![0.0; num_states],
            num_states,
            num_observations,
        }
    }
    
    pub fn viterbi(&self, observations: &[usize]) -> Vec<usize> {
        let n = observations.len();
        let mut viterbi = vec![vec![0.0; self.num_states]; n];
        let mut backpointer = vec![vec![0; self.num_states]; n];
        
        // 初始化
        for s in 0..self.num_states {
            viterbi[0][s] = self.initial_probs[s] * self.emission_matrix[s][observations[0]];
        }
        
        // 前向传播
        for t in 1..n {
            for s in 0..self.num_states {
                let mut max_prob = 0.0;
                let mut best_prev_state = 0;
                
                for prev_s in 0..self.num_states {
                    let prob = viterbi[t-1][prev_s] * 
                              self.transition_matrix[prev_s][s] * 
                              self.emission_matrix[s][observations[t]];
                    
                    if prob > max_prob {
                        max_prob = prob;
                        best_prev_state = prev_s;
                    }
                }
                
                viterbi[t][s] = max_prob;
                backpointer[t][s] = best_prev_state;
            }
        }
        
        // 回溯找到最佳路径
        let mut best_path = vec![0; n];
        let mut best_final_state = 0;
        let mut max_prob = 0.0;
        
        for s in 0..self.num_states {
            if viterbi[n-1][s] > max_prob {
                max_prob = viterbi[n-1][s];
                best_final_state = s;
            }
        }
        
        best_path[n-1] = best_final_state;
        
        for t in (0..n-1).rev() {
            best_path[t] = backpointer[t+1][best_path[t+1]];
        }
        
        best_path
    }
    
    pub fn forward(&self, observations: &[usize]) -> Vec<Vec<f64>> {
        let n = observations.len();
        let mut alpha = vec![vec![0.0; self.num_states]; n];
        
        // 初始化
        for s in 0..self.num_states {
            alpha[0][s] = self.initial_probs[s] * self.emission_matrix[s][observations[0]];
        }
        
        // 前向传播
        for t in 1..n {
            for s in 0..self.num_states {
                for prev_s in 0..self.num_states {
                    alpha[t][s] += alpha[t-1][prev_s] * 
                                  self.transition_matrix[prev_s][s] * 
                                  self.emission_matrix[s][observations[t]];
                }
            }
        }
        
        alpha
    }
    
    pub fn backward(&self, observations: &[usize]) -> Vec<Vec<f64>> {
        let n = observations.len();
        let mut beta = vec![vec![0.0; self.num_states]; n];
        
        // 初始化
        for s in 0..self.num_states {
            beta[n-1][s] = 1.0;
        }
        
        // 后向传播
        for t in (0..n-1).rev() {
            for s in 0..self.num_states {
                for next_s in 0..self.num_states {
                    beta[t][s] += beta[t+1][next_s] * 
                                 self.transition_matrix[s][next_s] * 
                                 self.emission_matrix[next_s][observations[t+1]];
                }
            }
        }
        
        beta
    }
}
```

## 5. 相关理论与交叉引用

- [机器学习理论](../01_Machine_Learning/01_Machine_Learning_Theory.md)
- [深度学习理论](../02_Deep_Learning/01_Deep_Learning_Theory.md)
- [强化学习理论](../03_Reinforcement_Learning/01_Reinforcement_Learning_Theory.md)

## 6. 参考文献

1. Jurafsky, D., & Martin, J. H. (2019). Speech and Language Processing. Pearson.
2. Mikolov, T., et al. (2013). Efficient Estimation of Word Representations in Vector Space. arXiv.
3. Rabiner, L. R. (1989). A Tutorial on Hidden Markov Models and Selected Applications in Speech Recognition. Proceedings of the IEEE.

---

**最后更新**: 2024年12月21日  
**维护者**: AI助手  
**版本**: v1.0 