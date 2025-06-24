# 1. 形式语法 (Formal Grammars)

## 1.1 概述

形式语法是形式语言理论的基础，用于描述和生成语言。在计算机科学中，形式语法为编译器设计、自然语言处理和程序验证提供了理论基础。

## 1.2 基本概念

### 1.2.1 字母表和字符串

**定义 1.1** (字母表)
字母表是有限符号的集合，通常记作 $\Sigma$。

**定义 1.2** (字符串)
字符串是字母表中符号的有限序列。空字符串记作 $\varepsilon$。

**定义 1.3** (字符串长度)
字符串 $w$ 的长度，记作 $|w|$，是字符串中符号的个数。

**定义 1.4** (字符串连接)
字符串 $u$ 和 $v$ 的连接，记作 $u \cdot v$ 或 $uv$，是将 $v$ 附加到 $u$ 末尾得到的字符串。

**定义 1.5** (字符串幂)
字符串 $w$ 的 $n$ 次幂定义为：
- $w^0 = \varepsilon$
- $w^n = w \cdot w^{n-1}$ 对于 $n > 0$

### 1.2.2 语言

**定义 1.6** (语言)
语言是字母表 $\Sigma$ 上字符串的集合：
$$L \subseteq \Sigma^*$$

其中 $\Sigma^*$ 表示 $\Sigma$ 上所有字符串的集合。

**定义 1.7** (语言的运算)

1. **并集**: $L_1 \cup L_2 = \{w \mid w \in L_1 \lor w \in L_2\}$
2. **交集**: $L_1 \cap L_2 = \{w \mid w \in L_1 \land w \in L_2\}$
3. **补集**: $\overline{L} = \Sigma^* \setminus L$
4. **连接**: $L_1 \cdot L_2 = \{uv \mid u \in L_1 \land v \in L_2\}$
5. **幂**: $L^0 = \{\varepsilon\}$，$L^n = L \cdot L^{n-1}$ 对于 $n > 0$
6. **克林闭包**: $L^* = \bigcup_{n=0}^{\infty} L^n$
7. **正闭包**: $L^+ = \bigcup_{n=1}^{\infty} L^n$

## 1.3 形式语法

### 1.3.1 语法定义

**定义 1.8** (形式语法)
形式语法是一个四元组 $G = (V, \Sigma, P, S)$，其中：
- $V$ 是非终结符的有限集合
- $\Sigma$ 是终结符的有限集合，且 $V \cap \Sigma = \emptyset$
- $P$ 是产生式规则的有限集合
- $S \in V$ 是开始符号

**定义 1.9** (产生式规则)
产生式规则具有形式 $\alpha \rightarrow \beta$，其中：
- $\alpha \in (V \cup \Sigma)^* V (V \cup \Sigma)^*$
- $\beta \in (V \cup \Sigma)^*$

### 1.3.2 推导

**定义 1.10** (直接推导)
如果存在产生式规则 $\alpha \rightarrow \beta$，则称 $\gamma \alpha \delta$ 直接推导出 $\gamma \beta \delta$，记作：
$$\gamma \alpha \delta \Rightarrow \gamma \beta \delta$$

**定义 1.11** (推导)
如果存在字符串序列 $\alpha_0, \alpha_1, \ldots, \alpha_n$ 使得：
$$\alpha_0 \Rightarrow \alpha_1 \Rightarrow \cdots \Rightarrow \alpha_n$$

则称 $\alpha_0$ 推导出 $\alpha_n$，记作 $\alpha_0 \Rightarrow^* \alpha_n$。

**定义 1.12** (语言生成)
语法 $G$ 生成的语言定义为：
$$L(G) = \{w \in \Sigma^* \mid S \Rightarrow^* w\}$$

## 1.4 乔姆斯基层次

### 1.4.1 0型语法（无限制语法）

**定义 1.13** (0型语法)
0型语法对产生式规则没有限制，可以包含任意形式的规则。

**定理 1.1** (0型语法的表达能力)
0型语法可以生成所有递归可枚举语言。

### 1.4.2 1型语法（上下文相关语法）

**定义 1.14** (上下文相关语法)
1型语法的产生式规则具有形式：
$$\alpha A \beta \rightarrow \alpha \gamma \beta$$

其中 $A \in V$，$\alpha, \beta \in (V \cup \Sigma)^*$，$\gamma \in (V \cup \Sigma)^+$。

**定理 1.2** (上下文相关语法的性质)
1型语法生成的语言类包含在递归语言类中。

### 1.4.3 2型语法（上下文无关语法）

**定义 1.15** (上下文无关语法)
2型语法的产生式规则具有形式：
$$A \rightarrow \alpha$$

其中 $A \in V$，$\alpha \in (V \cup \Sigma)^*$。

**定义 1.16** (上下文无关语言)
由上下文无关语法生成的语言称为上下文无关语言。

**定理 1.3** (上下文无关语法的性质)
1. 上下文无关语言在并集、连接和克林闭包运算下封闭
2. 上下文无关语言在交集和补集运算下不封闭

### 1.4.4 3型语法（正则语法）

**定义 1.17** (右线性语法)
右线性语法的产生式规则具有形式：
$$A \rightarrow aB \quad \text{或} \quad A \rightarrow a$$

其中 $A, B \in V$，$a \in \Sigma$。

**定义 1.18** (左线性语法)
左线性语法的产生式规则具有形式：
$$A \rightarrow Ba \quad \text{或} \quad A \rightarrow a$$

其中 $A, B \in V$，$a \in \Sigma$。

**定义 1.19** (正则语法)
正则语法是右线性语法或左线性语法。

**定理 1.4** (正则语法的等价性)
右线性语法和左线性语法生成相同的语言类。

## 1.5 语法分析

### 1.5.1 语法树

**定义 1.20** (语法树)
语法树是表示推导过程的树形结构，其中：
- 根节点是开始符号
- 内部节点是非终结符
- 叶节点是终结符或空字符串
- 每个内部节点的子节点对应一个产生式规则

**定义 1.21** (最左推导)
最左推导是每次替换最左边的非终结符的推导过程。

**定义 1.22** (最右推导)
最右推导是每次替换最右边的非终结符的推导过程。

### 1.5.2 歧义性

**定义 1.23** (歧义语法)
如果存在字符串 $w$ 使得 $w$ 有多个不同的语法树，则称语法是歧义的。

**定义 1.24** (固有歧义语言)
如果语言 $L$ 的所有语法都是歧义的，则称 $L$ 是固有歧义的。

**定理 1.5** (歧义性判定)
歧义性问题是不可判定的。

## 1.6 语法变换

### 1.6.1 消除空产生式

**算法 1.1** (消除空产生式)
输入：上下文无关语法 $G = (V, \Sigma, P, S)$
输出：等价的上下文无关语法 $G'$，不包含空产生式（除了 $S \rightarrow \varepsilon$）

```rust
fn eliminate_epsilon_productions(grammar: &Grammar) -> Grammar {
    // 找出所有可以推导出空字符串的非终结符
    let nullable = find_nullable_nonterminals(grammar);
    
    // 生成新的产生式规则
    let mut new_productions = Vec::new();
    
    for production in &grammar.productions {
        let alternatives = generate_alternatives(&production.rhs, &nullable);
        for alt in alternatives {
            if !alt.is_empty() {
                new_productions.push(Production {
                    lhs: production.lhs.clone(),
                    rhs: alt,
                });
            }
        }
    }
    
    Grammar {
        variables: grammar.variables.clone(),
        terminals: grammar.terminals.clone(),
        productions: new_productions,
        start_symbol: grammar.start_symbol.clone(),
    }
}

fn find_nullable_nonterminals(grammar: &Grammar) -> HashSet<String> {
    let mut nullable = HashSet::new();
    let mut changed = true;
    
    while changed {
        changed = false;
        for production in &grammar.productions {
            if production.rhs.iter().all(|symbol| {
                symbol == "ε" || nullable.contains(symbol)
            }) {
                if nullable.insert(production.lhs.clone()) {
                    changed = true;
                }
            }
        }
    }
    
    nullable
}
```

### 1.6.2 消除单位产生式

**算法 1.2** (消除单位产生式)
输入：上下文无关语法 $G$
输出：等价的上下文无关语法 $G'$，不包含单位产生式

```rust
fn eliminate_unit_productions(grammar: &Grammar) -> Grammar {
    // 计算单位闭包
    let unit_closure = compute_unit_closure(grammar);
    
    // 生成新的产生式规则
    let mut new_productions = Vec::new();
    
    for (nonterminal, reachable) in unit_closure {
        for production in &grammar.productions {
            if production.lhs == nonterminal && production.rhs.len() > 1 {
                for reachable_nt in reachable {
                    new_productions.push(Production {
                        lhs: reachable_nt,
                        rhs: production.rhs.clone(),
                    });
                }
            }
        }
    }
    
    Grammar {
        variables: grammar.variables.clone(),
        terminals: grammar.terminals.clone(),
        productions: new_productions,
        start_symbol: grammar.start_symbol.clone(),
    }
}
```

### 1.6.3 乔姆斯基范式

**定义 1.25** (乔姆斯基范式)
上下文无关语法是乔姆斯基范式，如果所有产生式规则都具有形式：
- $A \rightarrow BC$，其中 $A, B, C \in V$
- $A \rightarrow a$，其中 $A \in V$，$a \in \Sigma$
- $S \rightarrow \varepsilon$（仅当 $\varepsilon \in L(G)$）

**算法 1.3** (转换为乔姆斯基范式)
输入：上下文无关语法 $G$
输出：等价的乔姆斯基范式语法 $G'$

```rust
fn convert_to_chomsky_normal_form(grammar: &Grammar) -> Grammar {
    // 步骤1：消除空产生式
    let mut g1 = eliminate_epsilon_productions(grammar);
    
    // 步骤2：消除单位产生式
    let mut g2 = eliminate_unit_productions(&g1);
    
    // 步骤3：消除长产生式
    let mut g3 = eliminate_long_productions(&g2);
    
    // 步骤4：消除混合产生式
    let g4 = eliminate_mixed_productions(&g3);
    
    g4
}

fn eliminate_long_productions(grammar: &Grammar) -> Grammar {
    let mut new_productions = Vec::new();
    let mut new_variables = grammar.variables.clone();
    let mut counter = 0;
    
    for production in &grammar.productions {
        if production.rhs.len() > 2 {
            // 引入新的非终结符来分解长产生式
            let mut current_lhs = production.lhs.clone();
            
            for i in 0..production.rhs.len() - 2 {
                let new_var = format!("X{}", counter);
                counter += 1;
                new_variables.insert(new_var.clone());
                
                new_productions.push(Production {
                    lhs: current_lhs,
                    rhs: vec![production.rhs[i].clone(), new_var.clone()],
                });
                
                current_lhs = new_var;
            }
            
            new_productions.push(Production {
                lhs: current_lhs,
                rhs: vec![production.rhs[production.rhs.len() - 2].clone(), 
                         production.rhs[production.rhs.len() - 1].clone()],
            });
        } else {
            new_productions.push(production.clone());
        }
    }
    
    Grammar {
        variables: new_variables,
        terminals: grammar.terminals.clone(),
        productions: new_productions,
        start_symbol: grammar.start_symbol.clone(),
    }
}
```

## 1.7 语法在计算机科学中的应用

### 1.7.1 编译器设计

形式语法为编译器设计提供了理论基础：

```rust
// 简单的算术表达式语法
#[derive(Debug, Clone)]
enum Token {
    Number(i64),
    Plus,
    Minus,
    Multiply,
    Divide,
    LeftParen,
    RightParen,
    End,
}

#[derive(Debug)]
struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens, current: 0 }
    }
    
    fn parse_expression(&mut self) -> Result<i64, String> {
        let mut left = self.parse_term()?;
        
        while self.current < self.tokens.len() {
            match self.tokens[self.current] {
                Token::Plus => {
                    self.current += 1;
                    left += self.parse_term()?;
                }
                Token::Minus => {
                    self.current += 1;
                    left -= self.parse_term()?;
                }
                _ => break,
            }
        }
        
        Ok(left)
    }
    
    fn parse_term(&mut self) -> Result<i64, String> {
        let mut left = self.parse_factor()?;
        
        while self.current < self.tokens.len() {
            match self.tokens[self.current] {
                Token::Multiply => {
                    self.current += 1;
                    left *= self.parse_factor()?;
                }
                Token::Divide => {
                    self.current += 1;
                    let right = self.parse_factor()?;
                    if right == 0 {
                        return Err("Division by zero".to_string());
                    }
                    left /= right;
                }
                _ => break,
            }
        }
        
        Ok(left)
    }
    
    fn parse_factor(&mut self) -> Result<i64, String> {
        match self.tokens[self.current] {
            Token::Number(n) => {
                self.current += 1;
                Ok(n)
            }
            Token::LeftParen => {
                self.current += 1;
                let result = self.parse_expression()?;
                if let Token::RightParen = self.tokens[self.current] {
                    self.current += 1;
                    Ok(result)
                } else {
                    Err("Expected closing parenthesis".to_string())
                }
            }
            _ => Err("Expected number or opening parenthesis".to_string()),
        }
    }
}
```

### 1.7.2 自然语言处理

形式语法为自然语言处理提供了基础：

```rust
// 简单的自然语言语法分析器
#[derive(Debug, Clone)]
enum WordType {
    Noun,
    Verb,
    Adjective,
    Article,
    Preposition,
}

#[derive(Debug)]
struct Word {
    text: String,
    word_type: WordType,
}

#[derive(Debug)]
struct Sentence {
    subject: Option<String>,
    verb: Option<String>,
    object: Option<String>,
}

struct NaturalLanguageParser;

impl NaturalLanguageParser {
    fn parse_sentence(words: &[Word]) -> Result<Sentence, String> {
        let mut sentence = Sentence {
            subject: None,
            verb: None,
            object: None,
        };
        
        let mut i = 0;
        
        // 解析主语
        if i < words.len() {
            match words[i].word_type {
                WordType::Article => {
                    i += 1;
                    if i < words.len() {
                        match words[i].word_type {
                            WordType::Noun => {
                                sentence.subject = Some(words[i].text.clone());
                                i += 1;
                            }
                            _ => return Err("Expected noun after article".to_string()),
                        }
                    }
                }
                WordType::Noun => {
                    sentence.subject = Some(words[i].text.clone());
                    i += 1;
                }
                _ => return Err("Expected subject".to_string()),
            }
        }
        
        // 解析谓语
        if i < words.len() {
            match words[i].word_type {
                WordType::Verb => {
                    sentence.verb = Some(words[i].text.clone());
                    i += 1;
                }
                _ => return Err("Expected verb".to_string()),
            }
        }
        
        // 解析宾语
        if i < words.len() {
            match words[i].word_type {
                WordType::Article => {
                    i += 1;
                    if i < words.len() {
                        match words[i].word_type {
                            WordType::Noun => {
                                sentence.object = Some(words[i].text.clone());
                                i += 1;
                            }
                            _ => return Err("Expected noun after article".to_string()),
                        }
                    }
                }
                WordType::Noun => {
                    sentence.object = Some(words[i].text.clone());
                    i += 1;
                }
                _ => return Err("Expected object".to_string()),
            }
        }
        
        Ok(sentence)
    }
}
```

### 1.7.3 形式化验证

在形式化验证中，语法用于规范描述：

```lean
-- Lean 中的语法定义
inductive Token
| number : ℕ → Token
| plus : Token
| minus : Token
| multiply : Token
| divide : Token
| left_paren : Token
| right_paren : Token

inductive Expression
| number : ℕ → Expression
| add : Expression → Expression → Expression
| subtract : Expression → Expression → Expression
| multiply : Expression → Expression → Expression
| divide : Expression → Expression → Expression

-- 语法解析函数
def parse_expression (tokens : list Token) : option Expression :=
  -- 实现语法解析
  none

-- 语法正确性定理
theorem parse_correctness (tokens : list Token) (expr : Expression) :
  parse_expression tokens = some expr →
  -- 解析结果满足语法规则
  true :=
begin
  -- 证明实现
  sorry
end
```

## 1.8 总结

形式语法为形式科学提供了重要的理论基础：

1. **语法层次** 为语言分类提供了清晰的框架
2. **语法分析** 为语言处理提供了算法基础
3. **语法变换** 为语法优化提供了工具
4. **应用领域** 涵盖了编译器、自然语言处理和形式化验证

这些理论不仅在理论计算机科学中具有重要地位，也为实际应用提供了基础。

## 参考文献

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). *Introduction to automata theory, languages, and computation*. Pearson.
2. Sipser, M. (2012). *Introduction to the theory of computation*. Cengage Learning.
3. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). *Compilers: Principles, techniques, and tools*. Pearson.
4. Chomsky, N. (1956). Three models for the description of language. *IRE Transactions on information theory*, 2(3), 113-124.

---

**更新时间**: 2024-12-21  
**版本**: 1.0  
**作者**: FormalScience Team 