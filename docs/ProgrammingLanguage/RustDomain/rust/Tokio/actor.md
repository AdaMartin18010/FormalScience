# Rust-Actor模式实现

我将为您展示一个基于 Rust 2024 + Actor 模式的算法和数据结构实现。

## 目录

- [Rust-Actor模式实现](#rust-actor模式实现)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
  - [2. Actor 基础结构实现](#2-actor-基础结构实现)
    - [3. 树结构 Actor 实现](#3-树结构-actor-实现)
    - [4. 图结构 Actor 实现](#4-图结构-actor-实现)
    - [5. 排序算法 Actor 实现](#5-排序算法-actor-实现)
    - [6. 搜索算法 Actor 实现](#6-搜索算法-actor-实现)
    - [7. 主程序实现](#7-主程序实现)

## 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
actix = "0.13"
async-stream = "0.3"
futures = "0.3"
dashmap = "5.5"
parking_lot = "0.12"
tracing = "0.1"
```

## 2. Actor 基础结构实现

```rust
use actix::{Actor, Context, Handler, Message};
use async_stream::try_stream;
use std::collections::VecDeque;

/// 定义基础的 Actor 消息类型
#[derive(Message)]
#[rtype(result = "Result<(), ActorError>")]
pub enum DataStructureMessage<T> {
    Insert(T),
    Remove(T),
    Contains(T),
    Clear,
    Size,
}

/// 定义算法操作消息
#[derive(Message)]
#[rtype(result = "Result<Vec<T>, ActorError>")]
pub enum AlgorithmMessage<T> {
    Sort(Vec<T>),
    Search(Vec<T>, T),
    PathFind(Graph<T>, Node<T>, Node<T>),
}

/// Actor 错误类型
#[derive(Debug, thiserror::Error)]
pub enum ActorError {
    #[error("Operation failed: {0}")]
    OperationFailed(String),
    #[error("Invalid input: {0}")]
    InvalidInput(String),
}

/// 基础 Actor 特征
#[async_trait]
pub trait DataStructureActor<T>: Actor {
    /// 使用生成器处理操作流
    fn handle_operations(&mut self) -> impl Stream<Item = Result<(), ActorError>> {
        try_stream! {
            while let Some(msg) = self.receive().await {
                match msg {
                    DataStructureMessage::Insert(item) => {
                        self.insert(item).await?;
                        yield Ok(());
                    }
                    DataStructureMessage::Remove(item) => {
                        self.remove(item).await?;
                        yield Ok(());
                    }
                    // ... 其他操作
                }
            }
        }
    }

    async fn insert(&mut self, item: T) -> Result<(), ActorError>;
    async fn remove(&mut self, item: T) -> Result<(), ActorError>;
    async fn contains(&self, item: &T) -> Result<bool, ActorError>;
}
```

### 3. 树结构 Actor 实现

```rust
/// 二叉树节点
pub struct TreeNode<T> {
    value: T,
    left: Option<Box<TreeNode<T>>>,
    right: Option<Box<TreeNode<T>>>,
}

/// 二叉树 Actor
pub struct BinaryTreeActor<T> {
    root: Option<Box<TreeNode<T>>>,
    size: usize,
}

impl<T: 'static + Send + Sync + Ord> Actor for BinaryTreeActor<T> {
    type Context = Context<Self>;

    fn started(&mut self, ctx: &mut Self::Context) {
        // 初始化树结构
        tracing::info!("BinaryTreeActor started");
    }
}

impl<T: 'static + Send + Sync + Ord> Handler<DataStructureMessage<T>> for BinaryTreeActor<T> {
    type Result = Result<(), ActorError>;

    fn handle(&mut self, msg: DataStructureMessage<T>, _: &mut Context<Self>) -> Self::Result {
        // 使用生成器处理树操作
        let mut operations = try_stream! {
            match msg {
                DataStructureMessage::Insert(value) => {
                    self.insert_with_generator(value).await?;
                }
                DataStructureMessage::Remove(value) => {
                    self.remove_with_generator(value).await?;
                }
                // ... 其他操作
            }
            yield Ok(());
        };

        // 执行操作流
        while let Some(result) = operations.next().await {
            result?;
        }

        Ok(())
    }
}

impl<T: Ord> BinaryTreeActor<T> {
    /// 使用生成器实现插入操作
    async fn insert_with_generator(&mut self, value: T) -> Result<(), ActorError> {
        let mut insertion = try_stream! {
            let mut current = &mut self.root;
            
            while let Some(node) = current {
                if value < node.value {
                    current = &mut node.left;
                } else {
                    current = &mut node.right;
                }
                yield ();
            }

            *current = Some(Box::new(TreeNode {
                value,
                left: None,
                right: None,
            }));
            
            self.size += 1;
        };

        while let Some(_) = insertion.next().await {}
        Ok(())
    }

    /// 使用生成器实现中序遍历
    pub fn inorder_traversal(&self) -> impl Stream<Item = &T> {
        try_stream! {
            let mut stack = Vec::new();
            let mut current = &self.root;

            while !stack.is_empty() || current.is_some() {
                while let Some(node) = current {
                    stack.push(node);
                    current = &node.left;
                    yield ();
                }

                if let Some(node) = stack.pop() {
                    yield &node.value;
                    current = &node.right;
                }
            }
        }
    }
}
```

### 4. 图结构 Actor 实现

```rust
/// 图节点
pub struct GraphNode<T> {
    value: T,
    edges: Vec<(usize, f64)>, // (目标节点索引, 权重)
}

/// 图 Actor
pub struct GraphActor<T> {
    nodes: Vec<GraphNode<T>>,
    size: usize,
}

impl<T: 'static + Send + Sync + Eq> Actor for GraphActor<T> {
    type Context = Context<Self>;
}

impl<T: 'static + Send + Sync + Eq> Handler<AlgorithmMessage<T>> for GraphActor<T> {
    type Result = Result<Vec<T>, ActorError>;

    fn handle(&mut self, msg: AlgorithmMessage<T>, _: &mut Context<Self>) -> Self::Result {
        // 使用生成器实现图算法
        let mut algorithm = match msg {
            AlgorithmMessage::PathFind(start, end) => {
                self.dijkstra_with_generator(start, end)
            }
            // ... 其他算法
        };

        // 执行算法流
        let mut result = Vec::new();
        while let Some(node) = algorithm.next().await {
            result.push(node?);
        }

        Ok(result)
    }
}

impl<T: Eq> GraphActor<T> {
    /// 使用生成器实现 Dijkstra 最短路径算法
    fn dijkstra_with_generator(
        &self,
        start: usize,
        end: usize,
    ) -> impl Stream<Item = Result<T, ActorError>> {
        try_stream! {
            let mut distances = vec![f64::INFINITY; self.size];
            let mut previous = vec![None; self.size];
            let mut visited = vec![false; self.size];
            
            distances[start] = 0.0;

            for _ in 0..self.size {
                // 找到最近的未访问节点
                let mut min_distance = f64::INFINITY;
                let mut current = None;

                for i in 0..self.size {
                    if !visited[i] && distances[i] < min_distance {
                        min_distance = distances[i];
                        current = Some(i);
                    }
                }

                let current = current.ok_or(ActorError::OperationFailed(
                    "No path found".to_string(),
                ))?;

                if current == end {
                    break;
                }

                visited[current] = true;

                // 更新邻居节点的距离
                for &(neighbor, weight) in &self.nodes[current].edges {
                    let distance = distances[current] + weight;
                    if distance < distances[neighbor] {
                        distances[neighbor] = distance;
                        previous[neighbor] = Some(current);
                    }
                }

                yield Ok(self.nodes[current].value.clone());
            }

            // 构建路径
            let mut path = Vec::new();
            let mut current = end;
            while let Some(prev) = previous[current] {
                path.push(self.nodes[current].value.clone());
                current = prev;
            }
            path.push(self.nodes[start].value.clone());
            path.reverse();

            for node in path {
                yield Ok(node);
            }
        }
    }
}
```

### 5. 排序算法 Actor 实现

```rust
/// 排序 Actor
pub struct SortingActor<T> {
    phantom: std::marker::PhantomData<T>,
}

impl<T: 'static + Send + Sync + Ord> Actor for SortingActor<T> {
    type Context = Context<Self>;
}

impl<T: 'static + Send + Sync + Ord> Handler<AlgorithmMessage<T>> for SortingActor<T> {
    type Result = Result<Vec<T>, ActorError>;

    fn handle(&mut self, msg: AlgorithmMessage<T>, _: &mut Context<Self>) -> Self::Result {
        match msg {
            AlgorithmMessage::Sort(mut items) => {
                // 使用生成器实现快速排序
                let mut sort = self.quicksort_with_generator(&mut items);
                while let Some(_) = sort.next().await {}
                Ok(items)
            }
            // ... 其他排序算法
        }
    }
}

impl<T: Ord> SortingActor<T> {
    /// 使用生成器实现快速排序
    fn quicksort_with_generator(&self, arr: &mut [T]) -> impl Stream<Item = ()> {
        try_stream! {
            if arr.len() <= 1 {
                return;
            }

            let pivot = arr.len() - 1;
            let mut i = 0;

            for j in 0..pivot {
                if arr[j] <= arr[pivot] {
                    arr.swap(i, j);
                    i += 1;
                    yield ();
                }
            }

            arr.swap(i, pivot);

            // 递归排序左右子数组
            let (left, right) = arr.split_at_mut(i);
            let mut left_sort = self.quicksort_with_generator(left);
            let mut right_sort = self.quicksort_with_generator(&mut right[1..]);

            while let Some(_) = left_sort.next().await {}
            while let Some(_) = right_sort.next().await {}
        }
    }
}
```

### 6. 搜索算法 Actor 实现

```rust
/// 搜索 Actor
pub struct SearchActor<T> {
    phantom: std::marker::PhantomData<T>,
}

impl<T: 'static + Send + Sync + Ord> Actor for SearchActor<T> {
    type Context = Context<Self>;
}

impl<T: 'static + Send + Sync + Ord> Handler<AlgorithmMessage<T>> for SearchActor<T> {
    type Result = Result<Option<usize>, ActorError>;

    fn handle(&mut self, msg: AlgorithmMessage<T>, _: &mut Context<Self>) -> Self::Result {
        match msg {
            AlgorithmMessage::Search(items, target) => {
                // 使用生成器实现二分查找
                let mut search = self.binary_search_with_generator(&items, target);
                let mut result = None;
                
                while let Some(index) = search.next().await {
                    result = Some(index?);
                }
                
                Ok(result)
            }
            // ... 其他搜索算法
        }
    }
}

impl<T: Ord> SearchActor<T> {
    /// 使用生成器实现二分查找
    fn binary_search_with_generator(
        &self,
        arr: &[T],
        target: T,
    ) -> impl Stream<Item = Result<usize, ActorError>> {
        try_stream! {
            let mut left = 0;
            let mut right = arr.len();

            while left < right {
                let mid = left + (right - left) / 2;
                yield Ok(mid);

                match arr[mid].cmp(&target) {
                    std::cmp::Ordering::Equal => {
                        yield Ok(mid);
                        return;
                    }
                    std::cmp::Ordering::Less => left = mid + 1,
                    std::cmp::Ordering::Greater => right = mid,
                }
            }

            yield Err(ActorError::OperationFailed("Item not found".to_string()));
        }
    }
}
```

### 7. 主程序实现

```rust
#[tokio::main]
async fn main() -> Result<(), ActorError> {
    // 创建 Actor 系统
    let system = actix::System::new();

    // 启动数据结构 Actors
    let tree_actor = BinaryTreeActor::<i32>::new().start();
    let graph_actor = GraphActor::<i32>::new().start();

    // 启动算法 Actors
    let sort_actor = SortingActor::<i32>::new().start();
    let search_actor = SearchActor::<i32>::new().start();

    // 使用树结构
    tree_actor
        .send(DataStructureMessage::Insert(5))
        .await??;
    tree_actor
        .send(DataStructureMessage::Insert(3))
        .await??;
    tree_actor
        .send(DataStructureMessage::Insert(7))
        .await??;

    // 执行排序
    let unsorted = vec![5, 2, 8, 1, 9, 3];
    let sorted = sort_actor
        .send(AlgorithmMessage::Sort(unsorted))
        .await??;
    println!("Sorted array: {:?}", sorted);

    // 执行搜索
    let result = search_actor
        .send(AlgorithmMessage::Search(sorted, 5))
        .await??;
    println!("Found 5 at position: {:?}", result);

    // 图算法示例
    let path = graph_actor
        .send(AlgorithmMessage::PathFind(0, 5))
        .await??;
    println!("Shortest path: {:?}", path);

    system.run()?;
    Ok(())
}
```

这个实现提供了以下特性：

1. Actor 模式：
   - 消息传递
   - 状态隔离
   - 并发处理

2. 数据结构：
   - 二叉树
   - 图
   - 队列
   - 栈

3. 算法：
   - 排序算法
   - 搜索算法
   - 图算法
   - 路径查找

4. 生成器特性：
   - 异步流
   - 惰性计算
   - 迭代控制

5. 并发处理：
   - 异步操作
   - 消息队列
   - 状态管理

这个系统可以用于：

- 高性能数据处理
- 并发算法实现
- 分布式计算
- 实时数据分析

所有实现都充分利用了 Rust 的异步特性、Actor 模式和生成器机制，提供了高效的算法和数据结构处理能力。
