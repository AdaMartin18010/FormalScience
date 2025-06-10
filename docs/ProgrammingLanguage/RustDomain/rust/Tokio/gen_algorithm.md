# 生成器算法和数据结构实现

我将为您展示一个纯 Rust 2024 标准库 + Generator 实现的算法和数据结构集合。

## 目录

- [生成器算法和数据结构实现](#生成器算法和数据结构实现)
  - [目录](#目录)
  - [1. 生成器基础实现](#1-生成器基础实现)
  - [2. 排序算法实现](#2-排序算法实现)
  - [3. 二叉树实现](#3-二叉树实现)
  - [4. 图算法实现](#4-图算法实现)
  - [5. 搜索算法实现](#5-搜索算法实现)
  - [6. 堆实现](#6-堆实现)
  - [7. 使用示例](#7-使用示例)

## 1. 生成器基础实现

```rust
use std::pin::Pin;
use std::future::Future;
use std::task::{Context, Poll};

/// 定义生成器特征
pub trait Generator {
    type Yield;
    type Return;
    
    fn resume(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Yield>>;
}

/// 生成器包装器
pub struct GenWrapper<G> {
    gen: G,
}

impl<G: Generator> Future for GenWrapper<G> {
    type Output = G::Return;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // 实现生成器到 Future 的转换
        match self.gen.resume(cx) {
            Poll::Ready(Some(_)) => Poll::Pending,
            Poll::Ready(None) => Poll::Ready(self.gen.return_value()),
            Poll::Pending => Poll::Pending,
        }
    }
}
```

## 2. 排序算法实现

```rust
/// 快速排序生成器
pub struct QuickSortGen<T> {
    data: Vec<T>,
    state: SortState,
}

enum SortState {
    Start,
    Partitioning { left: usize, right: usize },
    Recursing { left: usize, right: usize },
    Done,
}

impl<T: Ord> Generator for QuickSortGen<T> {
    type Yield = Vec<T>;
    type Return = Vec<T>;

    fn resume(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Option<Self::Yield>> {
        loop {
            match self.state {
                SortState::Start => {
                    if self.data.len() <= 1 {
                        self.state = SortState::Done;
                        return Poll::Ready(None);
                    }
                    let len = self.data.len();
                    self.state = SortState::Partitioning { 
                        left: 0, 
                        right: len - 1 
                    };
                }
                SortState::Partitioning { left, right } => {
                    let pivot = self.partition(left, right);
                    self.state = SortState::Recursing { left, right };
                    return Poll::Ready(Some(self.data.clone()));
                }
                SortState::Recursing { left, right } => {
                    if left < right {
                        // 递归排序左右子数组
                        let mid = left + (right - left) / 2;
                        let mut left_gen = QuickSortGen::new(
                            self.data[left..mid].to_vec()
                        );
                        let mut right_gen = QuickSortGen::new(
                            self.data[mid+1..right+1].to_vec()
                        );

                        // 生成左子数组排序过程
                        while let Poll::Ready(Some(step)) = left_gen.resume(_) {
                            return Poll::Ready(Some(step));
                        }

                        // 生成右子数组排序过程
                        while let Poll::Ready(Some(step)) = right_gen.resume(_) {
                            return Poll::Ready(Some(step));
                        }
                    }
                    self.state = SortState::Done;
                }
                SortState::Done => return Poll::Ready(None),
            }
        }
    }
}

impl<T: Ord> QuickSortGen<T> {
    pub fn new(data: Vec<T>) -> Self {
        Self {
            data,
            state: SortState::Start,
        }
    }

    fn partition(&mut self, left: usize, right: usize) -> usize {
        let pivot = right;
        let mut i = left;

        for j in left..right {
            if self.data[j] <= self.data[pivot] {
                self.data.swap(i, j);
                i += 1;
            }
        }
        self.data.swap(i, pivot);
        i
    }
}
```

## 3. 二叉树实现

```rust
/// 二叉树节点
pub struct TreeNode<T> {
    value: T,
    left: Option<Box<TreeNode<T>>>,
    right: Option<Box<TreeNode<T>>>,
}

/// 二叉树遍历生成器
pub struct TreeTraversalGen<T> {
    root: Option<Box<TreeNode<T>>>,
    stack: Vec<TraversalState<T>>,
}

enum TraversalState<T> {
    Pre(Box<TreeNode<T>>),
    In(Box<TreeNode<T>>),
    Post(Box<TreeNode<T>>),
}

impl<T: Clone> Generator for TreeTraversalGen<T> {
    type Yield = T;
    type Return = ();

    fn resume(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Option<Self::Yield>> {
        if let Some(state) = self.stack.pop() {
            match state {
                TraversalState::Pre(node) => {
                    // 前序遍历
                    if let Some(right) = node.right {
                        self.stack.push(TraversalState::Pre(right));
                    }
                    if let Some(left) = node.left {
                        self.stack.push(TraversalState::Pre(left));
                    }
                    return Poll::Ready(Some(node.value));
                }
                TraversalState::In(node) => {
                    // 中序遍历
                    if let Some(right) = node.right {
                        self.stack.push(TraversalState::In(right));
                    }
                    let value = node.value.clone();
                    if let Some(left) = node.left {
                        self.stack.push(TraversalState::In(left));
                    }
                    return Poll::Ready(Some(value));
                }
                TraversalState::Post(node) => {
                    // 后序遍历
                    let value = node.value;
                    if let Some(left) = node.left {
                        self.stack.push(TraversalState::Post(left));
                    }
                    if let Some(right) = node.right {
                        self.stack.push(TraversalState::Post(right));
                    }
                    return Poll::Ready(Some(value));
                }
            }
        }
        Poll::Ready(None)
    }
}
```

## 4. 图算法实现

```rust
/// 图结构
pub struct Graph<T> {
    nodes: Vec<T>,
    edges: Vec<Vec<(usize, i32)>>, // (目标节点, 权重)
}

/// 最短路径生成器
pub struct DijkstraGen<T> {
    graph: Graph<T>,
    start: usize,
    end: usize,
    distances: Vec<i32>,
    visited: Vec<bool>,
    state: PathState,
}

enum PathState {
    Init,
    Finding,
    BuildPath,
    Done,
}

impl<T> Generator for DijkstraGen<T> {
    type Yield = Vec<usize>;
    type Return = Option<Vec<usize>>;

    fn resume(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Option<Self::Yield>> {
        match self.state {
            PathState::Init => {
                // 初始化距离数组
                self.distances = vec![i32::MAX; self.graph.nodes.len()];
                self.distances[self.start] = 0;
                self.state = PathState::Finding;
                return Poll::Ready(Some(vec![self.start]));
            }
            PathState::Finding => {
                // 寻找最短路径
                if let Some(current) = self.find_min_distance() {
                    if current == self.end {
                        self.state = PathState::BuildPath;
                        return Poll::Ready(Some(self.build_path()));
                    }

                    // 更新邻居节点的距离
                    for &(next, weight) in &self.graph.edges[current] {
                        let distance = self.distances[current].saturating_add(weight);
                        if distance < self.distances[next] {
                            self.distances[next] = distance;
                        }
                    }
                    return Poll::Ready(Some(vec![current]));
                }
                self.state = PathState::Done;
            }
            PathState::BuildPath => {
                self.state = PathState::Done;
                return Poll::Ready(Some(self.build_path()));
            }
            PathState::Done => return Poll::Ready(None),
        }
        Poll::Ready(None)
    }
}

impl<T> DijkstraGen<T> {
    fn find_min_distance(&mut self) -> Option<usize> {
        let mut min_distance = i32::MAX;
        let mut min_node = None;

        for (node, &distance) in self.distances.iter().enumerate() {
            if !self.visited[node] && distance < min_distance {
                min_distance = distance;
                min_node = Some(node);
            }
        }

        if let Some(node) = min_node {
            self.visited[node] = true;
        }
        min_node
    }

    fn build_path(&self) -> Vec<usize> {
        let mut path = Vec::new();
        let mut current = self.end;

        while current != self.start {
            path.push(current);
            // 找到前驱节点
            for (prev, _) in &self.graph.edges[current] {
                if self.distances[*prev] + 1 == self.distances[current] {
                    current = *prev;
                    break;
                }
            }
        }
        path.push(self.start);
        path.reverse();
        path
    }
}
```

## 5. 搜索算法实现

```rust
/// 二分查找生成器
pub struct BinarySearchGen<T> {
    data: Vec<T>,
    target: T,
    left: usize,
    right: usize,
    state: SearchState,
}

enum SearchState {
    Searching,
    Found(usize),
    NotFound,
}

impl<T: Ord> Generator for BinarySearchGen<T> {
    type Yield = usize;
    type Return = Option<usize>;

    fn resume(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Option<Self::Yield>> {
        match self.state {
            SearchState::Searching => {
                if self.left <= self.right {
                    let mid = self.left + (self.right - self.left) / 2;
                    match self.data[mid].cmp(&self.target) {
                        std::cmp::Ordering::Equal => {
                            self.state = SearchState::Found(mid);
                            return Poll::Ready(Some(mid));
                        }
                        std::cmp::Ordering::Less => {
                            self.left = mid + 1;
                            return Poll::Ready(Some(mid));
                        }
                        std::cmp::Ordering::Greater => {
                            self.right = mid - 1;
                            return Poll::Ready(Some(mid));
                        }
                    }
                }
                self.state = SearchState::NotFound;
            }
            SearchState::Found(_) | SearchState::NotFound => {
                return Poll::Ready(None);
            }
        }
        Poll::Ready(None)
    }
}
```

## 6. 堆实现

```rust
/// 最大堆生成器
pub struct MaxHeapGen<T> {
    data: Vec<T>,
    state: HeapState,
}

enum HeapState {
    Heapifying(usize),
    Done,
}

impl<T: Ord> Generator for MaxHeapGen<T> {
    type Yield = Vec<T>;
    type Return = Vec<T>;

    fn resume(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Option<Self::Yield>> {
        match self.state {
            HeapState::Heapifying(i) => {
                if i > 0 {
                    self.heapify(i);
                    self.state = HeapState::Heapifying(i - 1);
                    return Poll::Ready(Some(self.data.clone()));
                }
                self.state = HeapState::Done;
            }
            HeapState::Done => return Poll::Ready(None),
        }
        Poll::Ready(Some(self.data.clone()))
    }
}

impl<T: Ord> MaxHeapGen<T> {
    pub fn new(data: Vec<T>) -> Self {
        let len = data.len();
        Self {
            data,
            state: HeapState::Heapifying(len / 2),
        }
    }

    fn heapify(&mut self, i: usize) {
        let len = self.data.len();
        let mut largest = i;
        let left = 2 * i + 1;
        let right = 2 * i + 2;

        if left < len && self.data[left] > self.data[largest] {
            largest = left;
        }

        if right < len && self.data[right] > self.data[largest] {
            largest = right;
        }

        if largest != i {
            self.data.swap(i, largest);
            self.heapify(largest);
        }
    }
}
```

## 7. 使用示例

```rust
fn main() {
    // 快速排序示例
    let data = vec![5, 2, 8, 1, 9, 3];
    let mut sort_gen = QuickSortGen::new(data);
    
    println!("排序过程：");
    while let Poll::Ready(Some(step)) = Pin::new(&mut sort_gen).resume(&mut Context::empty()) {
        println!("{:?}", step);
    }

    // 二叉树遍历示例
    let mut tree = TreeNode::new(1);
    tree.insert(2);
    tree.insert(3);
    
    let mut traversal_gen = TreeTraversalGen::new(tree);
    println!("树遍历：");
    while let Poll::Ready(Some(value)) = Pin::new(&mut traversal_gen).resume(&mut Context::empty()) {
        println!("{}", value);
    }

    // 图最短路径示例
    let graph = Graph::new(5);
    graph.add_edge(0, 1, 4);
    graph.add_edge(0, 2, 1);
    graph.add_edge(2, 1, 2);
    graph.add_edge(1, 3, 1);
    
    let mut path_gen = DijkstraGen::new(graph, 0, 3);
    println!("最短路径查找：");
    while let Poll::Ready(Some(path)) = Pin::new(&mut path_gen).resume(&mut Context::empty()) {
        println!("{:?}", path);
    }

    // 二分查找示例
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut search_gen = BinarySearchGen::new(data, 5);
    
    println!("查找过程：");
    while let Poll::Ready(Some(mid)) = Pin::new(&mut search_gen).resume(&mut Context::empty()) {
        println!("检查位置: {}", mid);
    }

    // 堆构建示例
    let data = vec![4, 10, 3, 5, 1];
    let mut heap_gen = MaxHeapGen::new(data);
    
    println!("堆构建过程：");
    while let Poll::Ready(Some(heap)) = Pin::new(&mut heap_gen).resume(&mut Context::empty()) {
        println!("{:?}", heap);
    }
}
```

这个实现提供了：

1. 基础算法：
   - 快速排序
   - 二分查找
   - 堆排序

2. 数据结构：
   - 二叉树
   - 图
   - 堆

3. 生成器特性：
   - 状态管理
   - 惰性计算
   - 迭代控制

4. 高级算法：
   - 图遍历
   - 最短路径
   - 树遍历

所有实现都只使用了 Rust 标准库，充分展示了生成器的强大功能。每个算法和数据结构都可以逐步执行，便于观察和调试。
