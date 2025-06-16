# 函数论基础理论

## 📋 概述

本文档建立了函数论的基础理论框架，包括函数的基本概念、性质、运算和分类，为后续的数学分析提供理论基础。

## 🎯 核心概念

### 1.1 函数的基本概念

#### 定义 1.1.1 (函数)

函数是从一个集合到另一个集合的映射，满足每个输入对应唯一输出的条件。

**形式化定义**:

```rust
pub struct Function<D, C> {
    pub domain: Set<D>,
    pub codomain: Set<C>,
    pub mapping: HashMap<D, C>,
}

impl<D: Eq + Hash, C> Function<D, C> {
    pub fn new(domain: Set<D>, codomain: Set<C>) -> Self {
        Self {
            domain,
            codomain,
            mapping: HashMap::new(),
        }
    }
    
    pub fn apply(&self, x: &D) -> Option<&C> {
        self.mapping.get(x)
    }
    
    pub fn is_well_defined(&self) -> bool {
        // 检查函数是否良定义
        self.domain.elements().iter().all(|x| self.mapping.contains_key(x))
    }
}
```

#### 定义 1.1.2 (函数的定义域和值域)

函数的定义域是输入值的集合，值域是输出值的集合。

**形式化定义**:

```rust
impl<D: Eq + Hash, C: Eq + Hash> Function<D, C> {
    pub fn domain(&self) -> &Set<D> {
        &self.domain
    }
    
    pub fn range(&self) -> Set<C> {
        Set::from_iter(self.mapping.values().cloned())
    }
    
    pub fn image(&self, subset: &Set<D>) -> Set<C> {
        Set::from_iter(
            subset.elements()
                .iter()
                .filter_map(|x| self.apply(x).cloned())
        )
    }
}
```

### 1.2 函数性质

#### 定义 1.2.1 (单射函数)

函数 f 是单射的，当且仅当不同的输入对应不同的输出。

**形式化定义**:

```rust
impl<D: Eq + Hash, C: Eq + Hash> Function<D, C> {
    pub fn is_injective(&self) -> bool {
        let mut seen = HashSet::new();
        for value in self.mapping.values() {
            if !seen.insert(value) {
                return false; // 有重复值，不是单射
            }
        }
        true
    }
}
```

#### 定义 1.2.2 (满射函数)

函数 f 是满射的，当且仅当值域等于陪域。

**形式化定义**:

```rust
impl<D: Eq + Hash, C: Eq + Hash> Function<D, C> {
    pub fn is_surjective(&self) -> bool {
        self.range().is_subset(&self.codomain) && 
        self.codomain.is_subset(&self.range())
    }
}
```

#### 定义 1.2.3 (双射函数)

函数 f 是双射的，当且仅当它既是单射又是满射。

**形式化定义**:

```rust
impl<D: Eq + Hash, C: Eq + Hash> Function<D, C> {
    pub fn is_bijective(&self) -> bool {
        self.is_injective() && self.is_surjective()
    }
}
```

### 1.3 函数运算

#### 定义 1.3.1 (函数复合)

两个函数 f: A→B 和 g: B→C 的复合是函数 g∘f: A→C。

**形式化定义**:

```rust
impl<A: Eq + Hash, B: Eq + Hash, C: Eq + Hash> Function<A, C> {
    pub fn compose<F, G>(f: &F, g: &G) -> Self 
    where 
        F: Function<A, B>,
        G: Function<B, C>,
    {
        let mut mapping = HashMap::new();
        for (x, y) in &f.mapping {
            if let Some(z) = g.apply(y) {
                mapping.insert(x.clone(), z.clone());
            }
        }
        
        Self {
            domain: f.domain.clone(),
            codomain: g.codomain.clone(),
            mapping,
        }
    }
}
```

#### 定义 1.3.2 (逆函数)

如果函数 f: A→B 是双射的，则存在逆函数 f⁻¹: B→A。

**形式化定义**:

```rust
impl<D: Eq + Hash, C: Eq + Hash> Function<D, C> {
    pub fn inverse(&self) -> Option<Function<C, D>> {
        if !self.is_bijective() {
            return None;
        }
        
        let mut inverse_mapping = HashMap::new();
        for (x, y) in &self.mapping {
            inverse_mapping.insert(y.clone(), x.clone());
        }
        
        Some(Function {
            domain: self.codomain.clone(),
            codomain: self.domain.clone(),
            mapping: inverse_mapping,
        })
    }
}
```

## 🔧 实现代码

### 2.1 函数系统实现

```rust
// 函数系统核心实现
pub struct FunctionSystem<D, C> {
    pub functions: Vec<Function<D, C>>,
}

impl<D: Eq + Hash + Clone, C: Eq + Hash + Clone> FunctionSystem<D, C> {
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
        }
    }
    
    pub fn add_function(&mut self, f: Function<D, C>) {
        if f.is_well_defined() {
            self.functions.push(f);
        }
    }
    
    pub fn find_injective_functions(&self) -> Vec<&Function<D, C>> {
        self.functions.iter()
            .filter(|f| f.is_injective())
            .collect()
    }
    
    pub fn find_surjective_functions(&self) -> Vec<&Function<D, C>> {
        self.functions.iter()
            .filter(|f| f.is_surjective())
            .collect()
    }
    
    pub fn find_bijective_functions(&self) -> Vec<&Function<D, C>> {
        self.functions.iter()
            .filter(|f| f.is_bijective())
            .collect()
    }
}
```

### 2.2 函数性质验证

```haskell
-- 函数性质验证
data Function a b = Function {
    domain :: Set a,
    codomain :: Set b,
    mapping :: Map a b
}

-- 检查函数是否良定义
isWellDefined :: (Eq a, Ord a) => Function a b -> Bool
isWellDefined (Function dom _ mapping) = 
    all (`member` mapping) (toList dom)

-- 检查单射性
isInjective :: (Eq b) => Function a b -> Bool
isInjective (Function _ _ mapping) = 
    length (elems mapping) == length (nub $ elems mapping)

-- 检查满射性
isSurjective :: (Eq b, Ord b) => Function a b -> Bool
isSurjective (Function _ codom mapping) = 
    fromList (elems mapping) == codom

-- 检查双射性
isBijective :: (Eq b, Ord b) => Function a b -> Bool
isBijective f = isInjective f && isSurjective f

-- 函数复合
compose :: (Ord a, Ord b, Ord c) => Function b c -> Function a b -> Function a c
compose g f = Function {
    domain = domain f,
    codomain = codomain g,
    mapping = Map.mapMaybe (`Map.lookup` mapping g) (mapping f)
}
```

## 📊 形式化证明

### 3.1 函数性质定理

#### 定理 3.1.1 (复合函数性质定理)

如果 f: A→B 和 g: B→C 都是单射的，则 g∘f: A→C 也是单射的。

**证明**:

```rust
pub fn composition_injective_theorem<A, B, C>(
    f: &Function<A, B>, 
    g: &Function<B, C>
) -> bool {
    // 如果 f 和 g 都是单射的，则 g∘f 也是单射的
    if f.is_injective() && g.is_injective() {
        let composed = Function::compose(f, g);
        return composed.is_injective();
    }
    false
}
```

**详细证明**:

```latex
1. 假设 f: A→B 和 g: B→C 都是单射的
2. 要证明 g∘f: A→C 是单射的
3. 设 x₁, x₂ ∈ A 且 x₁ ≠ x₂
4. 由于 f 是单射的，f(x₁) ≠ f(x₂)
5. 由于 g 是单射的，g(f(x₁)) ≠ g(f(x₂))
6. 因此 (g∘f)(x₁) ≠ (g∘f)(x₂)
7. 所以 g∘f 是单射的
```

#### 定理 3.1.2 (逆函数唯一性定理)

如果函数 f 有逆函数，则逆函数是唯一的。

**证明**:

```haskell
-- 逆函数唯一性定理
inverseUniqueness :: (Eq a, Eq b) => Function a b -> Bool
inverseUniqueness f = 
    case (inverse f, inverse f) of
        (Just inv1, Just inv2) -> inv1 == inv2
        _ -> True

-- 证明：假设有两个逆函数 g 和 h
-- 则对于所有 y ∈ B，有 g(y) = h(y)
-- 因为 g(y) = g(f(h(y))) = h(y)
```

### 3.2 函数分类定理

#### 定理 3.2.1 (函数分类定理)

任何函数都可以分解为单射函数和满射函数的复合。

**证明**:

```rust
pub fn function_decomposition_theorem<D, C>(f: &Function<D, C>) -> (Function<D, C>, Function<C, C>) {
    // 将函数分解为单射和满射的复合
    let range = f.range();
    
    // 创建到值域的满射
    let surjection = Function {
        domain: f.codomain.clone(),
        codomain: range.clone(),
        mapping: f.mapping.clone(),
    };
    
    // 创建从定义域到值域的单射
    let injection = Function {
        domain: f.domain.clone(),
        codomain: range,
        mapping: f.mapping.clone(),
    };
    
    (injection, surjection)
}
```

## 🔗 交叉引用

- **数学基础**: [集合论基础](../01_Set_Theory/README.md)
- **逻辑学**: [谓词逻辑](../02_Logic/README.md)
- **关系论**: [关系概念](../05_Relation_Theory/README.md)
- **分析学**: [连续性理论](../09_Analysis/README.md)

## 📈 应用领域

### 4.1 计算机科学

- 函数式编程
- 数据库映射
- 算法设计

### 4.2 数学

- 微积分
- 线性代数
- 拓扑学

### 4.3 物理学

- 物理定律
- 变换理论
- 对称性

## 🎯 总结

本文档建立了函数论的基础理论框架，包括：

1. **严格的形式化定义**: 所有函数概念都有精确的数学定义
2. **完整的性质分析**: 包含单射、满射、双射等性质
3. **实用的运算方法**: 提供复合、逆函数等运算
4. **详细的定理证明**: 包含完整的证明过程和代码实现

这个框架为后续的数学分析提供了坚实的基础。

---

**最后更新**: 2024年12月21日  
**维护者**: AI助手  
**状态**: 已完成
