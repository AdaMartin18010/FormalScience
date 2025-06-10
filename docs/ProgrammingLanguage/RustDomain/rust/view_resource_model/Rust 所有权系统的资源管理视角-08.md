# Rust 所有权系统的资源管理视角（续八）

## 目录

- [Rust 所有权系统的资源管理视角（续八）](#rust-所有权系统的资源管理视角续八)
  - [目录](#目录)
  - [所有权与机器学习系统](#所有权与机器学习系统)
    - [张量所有权模型](#张量所有权模型)
    - [梯度计算中的资源管理](#梯度计算中的资源管理)
    - [模型训练与推理优化](#模型训练与推理优化)
    - [自动微分与所有权转换](#自动微分与所有权转换)
  - [所有权与图形编程深度探索](#所有权与图形编程深度探索)
    - [图形管线资源安全](#图形管线资源安全)
    - [场景图所有权层次](#场景图所有权层次)
    - [实体组件系统中的所有权深析](#实体组件系统中的所有权深析)
    - [物理与碰撞系统中的借用模型](#物理与碰撞系统中的借用模型)
  - [所有权与形式方法学](#所有权与形式方法学)
    - [线性逻辑与所有权深度联系](#线性逻辑与所有权深度联系)
    - [分离逻辑扩展](#分离逻辑扩展)
    - [程序验证与所有权证明](#程序验证与所有权证明)
    - [智能合约与所有权安全](#智能合约与所有权安全)
  - [操作系统与所有权系统](#操作系统与所有权系统)
    - [内核资源管理](#内核资源管理)
    - [驱动开发安全模型](#驱动开发安全模型)
    - [权限系统与所有权映射](#权限系统与所有权映射)
    - [操作系统抽象层的所有权](#操作系统抽象层的所有权)

## 所有权与机器学习系统

### 张量所有权模型

Rust 所有权系统如何应用于机器学习框架中的张量操作：

1. **张量资源管理**
   - 高效管理大规模张量内存
   - 跨设备张量所有权转移（CPU/GPU）

2. **计算图中的所有权追踪**
   - 追踪张量在计算图中的所有权流动
   - 避免不必要的数据复制和传输

3. **零拷贝张量操作**
   - 使用所有权系统实现张量操作的零拷贝优化
   - 借用系统用于原位运算

```rust
// 张量所有权模型示例

// 1. 基础张量类型
struct Tensor<T> {
    data: Vec<T>,
    shape: Vec<usize>,
    device: Device,
}

enum Device {
    CPU,
    CUDA(usize), // GPU 设备 ID
}

impl<T: Clone + Default> Tensor<T> {
    // 创建新张量（拥有所有权）
    fn new(shape: Vec<usize>, device: Device) -> Self {
        let size = shape.iter().product();
        let data = vec![T::default(); size];
        
        Tensor { data, shape, device }
    }
    
    // 在不同设备间转移所有权
    fn to_device(self, device: Device) -> Self {
        if self.device == device {
            return self; // 已在目标设备上，避免转移
        }
        
        println!("将张量从 {:?} 移动到 {:?}", self.device, device);
        // 实际应用中会处理设备内存分配和数据传输
        
        Tensor {
            data: self.data,
            shape: self.shape,
            device,
        }
    }
    
    // 内存优化：视图创建（借用而非复制）
    fn view(&self) -> TensorView<T> {
        TensorView {
            data: &self.data,
            shape: self.shape.clone(),
            device: self.device.clone(),
        }
    }
    
    // 转移所有权的操作
    fn add(self, other: Self) -> Result<Self, &'static str> {
        if self.shape != other.shape {
            return Err("形状不匹配");
        }
        
        if self.device != other.device {
            return Err("设备不匹配");
        }
        
        println!("执行张量加法（消耗两个输入）");
        
        // 简化实现
        let mut result_data = self.data.clone();
        for (i, val) in other.data.iter().enumerate() {
            if i < result_data.len() {
                // 这里需要实际实现 T 类型的加法
                // result_data[i] += *val;
            }
        }
        
        Ok(Tensor {
            data: result_data,
            shape: self.shape,
            device: self.device,
        })
    }
    
    // 借用的操作
    fn add_inplace(&mut self, other: &Self) -> Result<(), &'static str> {
        if self.shape != other.shape {
            return Err("形状不匹配");
        }
        
        if self.device != other.device {
            return Err("设备不匹配");
        }
        
        println!("执行原位张量加法（修改第一个输入）");
        
        // 简化实现
        for (i, val) in other.data.iter().enumerate() {
            if i < self.data.len() {
                // 这里需要实际实现 T 类型的加法
                // self.data[i] += *val;
            }
        }
        
        Ok(())
    }
}

// 张量视图（借用数据而非拥有）
struct TensorView<'a, T> {
    data: &'a Vec<T>,
    shape: Vec<usize>,
    device: Device,
}

// 2. 计算图中的张量所有权
struct ComputeNode<T> {
    operation: Operation,
    inputs: Vec<TensorId>,
    output: TensorId,
    _phantom: std::marker::PhantomData<T>,
}

enum Operation {
    Add,
    Multiply,
    ReLU,
    Softmax,
}

type TensorId = usize;

struct ComputeGraph<T> {
    tensors: Vec<Option<Tensor<T>>>,
    nodes: Vec<ComputeNode<T>>,
}

impl<T: Clone + Default> ComputeGraph<T> {
    fn new() -> Self {
        ComputeGraph {
            tensors: Vec::new(),
            nodes: Vec::new(),
        }
    }
    
    // 添加张量并获取 ID
    fn add_tensor(&mut self, tensor: Tensor<T>) -> TensorId {
        let id = self.tensors.len();
        self.tensors.push(Some(tensor));
        id
    }
    
    // 创建计算节点，消耗输入张量所有权，生成输出张量
    fn add_operation(&mut self, op: Operation, inputs: Vec<TensorId>) -> Result<TensorId, &'static str> {
        // 检查输入是否有效
        for &id in &inputs {
            if id >= self.tensors.len() || self.tensors[id].is_none() {
                return Err("无效的张量 ID");
            }
        }
        
        // 创建输出张量（简化实现）
        let output_tensor = Tensor::new(vec![1, 1], Device::CPU); // 简化
        let output_id = self.add_tensor(output_tensor);
        
        // 添加计算节点
        let node = ComputeNode {
            operation: op,
            inputs,
            output: output_id,
            _phantom: std::marker::PhantomData,
        };
        
        self.nodes.push(node);
        Ok(output_id)
    }
    
    // 执行计算，移动所有权
    fn execute(&mut self, node_index: usize) -> Result<TensorId, &'static str> {
        if node_index >= self.nodes.len() {
            return Err("无效的节点索引");
        }
        
        let node = &self.nodes[node_index];
        let op = node.operation.clone();
        let inputs = node.inputs.clone();
        let output = node.output;
        
        match op {
            Operation::Add => {
                if inputs.len() != 2 {
                    return Err("Add 操作需要两个输入");
                }
                
                // 取出输入张量（转移所有权）
                let input1 = self.tensors[inputs[0]].take()
                    .ok_or("输入张量已被消费")?;
                let input2 = self.tensors[inputs[1]].take()
                    .ok_or("输入张量已被消费")?;
                
                // 执行操作
                let result = input1.add(input2)?;
                
                // 存储结果
                self.tensors[output] = Some(result);
            }
            // 其他操作类似实现
            _ => return Err("未实现的操作"),
        }
        
        Ok(output)
    }
}
```

### 梯度计算中的资源管理

所有权系统如何优化梯度计算中的资源管理：

1. **梯度计算的内存管理**
   - 使用所有权跟踪以优化梯度内存
   - 自动微分图中的资源重用

2. **反向传播中的借用模式**
   - 前向传播和反向传播中的借用关系
   - 使用引用避免复制中间激活值

3. **计算图优化与所有权**
   - 利用所有权信息进行计算图优化
   - 原位操作与展开优化

```rust
// 梯度计算中的所有权管理示例

// 1. 支持自动微分的张量
struct DiffTensor<T> {
    data: Tensor<T>,
    requires_grad: bool,
    grad: Option<Tensor<T>>,
    grad_fn: Option<Box<dyn FnOnce() -> Tensor<T>>>,
}

impl<T: Clone + Default> DiffTensor<T> {
    fn new(data: Tensor<T>, requires_grad: bool) -> Self {
        let grad = if requires_grad {
            // 创建与数据相同形状的零梯度
            Some(Tensor::new(data.shape.clone(), data.device.clone()))
        } else {
            None
        };
        
        DiffTensor {
            data,
            requires_grad,
            grad,
            grad_fn: None,
        }
    }
    
    // 设置梯度函数（闭包捕获输入张量的引用）
    fn set_grad_fn<F>(&mut self, grad_fn: F)
    where
        F: FnOnce() -> Tensor<T> + 'static,
    {
        if self.requires_grad {
            self.grad_fn = Some(Box::new(grad_fn));
        }
    }
    
    // 反向传播计算梯度
    fn backward(mut self) {
        if !self.requires_grad || self.grad_fn.is_none() {
            return;
        }
        
        // 初始化梯度为全1
        let mut grad = Tensor::new(self.data.shape.clone(), self.data.device.clone());
        // 实际实现中，应将 grad 填充为 1
        
        // 设置本张量的梯度
        self.grad = Some(grad);
        
        // 调用梯度函数计算上游梯度
        if let Some(grad_fn) = self.grad_fn.take() {
            let _upstream_grad = grad_fn();
            // 在实际实现中，上游梯度会传递给前面的张量
        }
    }
}

// 2. 自动微分操作示例
struct AutogradContext<T> {
    saved_tensors: Vec<Tensor<T>>,
}

impl<T: Clone + Default> AutogradContext<T> {
    fn new() -> Self {
        AutogradContext {
            saved_tensors: Vec::new(),
        }
    }
    
    // 保存反向传播所需的张量
    fn save_for_backward(&mut self, tensor: Tensor<T>) {
        self.saved_tensors.push(tensor);
    }
    
    // 获取保存的张量
    fn get_saved_tensor(&self, index: usize) -> Option<&Tensor<T>> {
        self.saved_tensors.get(index)
    }
}

// 3. 加法运算的自动微分实现
fn add_forward<T: Clone + Default>(
    a: DiffTensor<T>,
    b: DiffTensor<T>,
    ctx: &mut AutogradContext<T>
) -> Result<DiffTensor<T>, &'static str> {
    // 执行前向计算
    let result_data = a.data.clone().add(b.data.clone())?;
    
    // 确定是否需要梯度
    let requires_grad = a.requires_grad || b.requires_grad;
    
    // 创建结果张量
    let mut result = DiffTensor::new(result_data, requires_grad);
    
    if requires_grad {
        // 保存反向传播所需的信息
        if a.requires_grad {
            ctx.save_for_backward(a.data.clone());
        }
        if b.requires_grad {
            ctx.save_for_backward(b.data.clone());
        }
        
        // 设置梯度函数
        let ctx_clone = AutogradContext {
            saved_tensors: ctx.saved_tensors.clone(),
        };
        
        result.set_grad_fn(move || {
            // 简化的反向传播实现
            println!("计算加法操作的梯度");
            
            // 在实际实现中，会利用 ctx_clone 中保存的张量计算梯度
            // 并传播到输入张量 a 和 b
            
            Tensor::new(vec![1, 1], Device::CPU) // 简化返回
        });
    }
    
    Ok(result)
}

// 4. 内存优化与梯度检查点示例
struct CheckpointStrategy {
    max_memory: usize,
    segments: Vec<usize>,
}

impl CheckpointStrategy {
    fn new(max_memory: usize) -> Self {
        CheckpointStrategy {
            max_memory,
            segments: Vec::new(),
        }
    }
    
    // 决定哪些层需要保存激活值，哪些需要重计算
    fn optimize<T>(&mut self, model: &Vec<Layer<T>>, input_size: usize) {
        println!("优化梯度检查点策略，最大内存: {} MB", self.max_memory);
        
        // 根据内存约束和计算成本计算最佳检查点
        // 实际实现会更复杂，这里简化
        
        // 假设每隔几层设置一个检查点
        for i in (0..model.len()).step_by(3) {
            self.segments.push(i);
        }
        
        println!("设置检查点在层: {:?}", self.segments);
    }
    
    // 检查给定层是否是检查点
    fn is_checkpoint(&self, layer_index: usize) -> bool {
        self.segments.contains(&layer_index)
    }
}

// 网络层
struct Layer<T> {
    weights: Tensor<T>,
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Clone + Default> Layer<T> {
    fn forward(&self, input: &Tensor<T>) -> Tensor<T> {
        // 简化的前向传播
        println!("层前向传播");
        Tensor::new(vec![1, 1], Device::CPU)
    }
    
    fn backward(&self, grad: &Tensor<T>) -> Tensor<T> {
        // 简化的反向传播
        println!("层反向传播");
        Tensor::new(vec![1, 1], Device::CPU)
    }
}
```

### 模型训练与推理优化

所有权与借用在模型训练与推理中的优化应用：

1. **批处理与所有权共享**
   - 批处理中的数据所有权管理
   - 最小化内存拷贝的批处理实现

2. **推理优化与所有权**
   - 推理中的零拷贝数据流
   - 内存规划与所有权分析

3. **分布式训练中的所有权边界**
   - 节点间的所有权转移策略
   - 参数服务器与所有权共享模型

```rust
// 模型训练与推理优化示例

// 1. 批处理数据加载器
struct DataLoader<T> {
    dataset: Vec<T>,
    batch_size: usize,
    current_index: usize,
}

impl<T: Clone> DataLoader<T> {
    fn new(dataset: Vec<T>, batch_size: usize) -> Self {
        DataLoader {
            dataset,
            batch_size,
            current_index: 0,
        }
    }
    
    // 迭代器模式加载批次数据
    fn next_batch(&mut self) -> Option<Vec<T>> {
        if self.current_index >= self.dataset.len() {
            return None; // 数据集已遍历完
        }
        
        let end_index = std::cmp::min(
            self.current_index + self.batch_size,
            self.dataset.len()
        );
        
        // 创建批次（注意：实际实现中可能需要优化以避免不必要的克隆）
        let batch: Vec<T> = self.dataset[self.current_index..end_index]
            .iter()
            .cloned()
            .collect();
            
        self.current_index = end_index;
        
        Some(batch)
    }
    
    // 零拷贝加载（使用引用而非克隆）
    fn next_batch_view(&mut self) -> Option<&[T]> {
        if self.current_index >= self.dataset.len() {
            return None;
        }
        
        let end_index = std::cmp::min(
            self.current_index + self.batch_size,
            self.dataset.len()
        );
        
        let batch = &self.dataset[self.current_index..end_index];
        self.current_index = end_index;
        
        Some(batch)
    }
}

// 2. 优化推理会话
struct InferenceSession<T> {
    model: Model<T>,
    device: Device,
    optimized_buffers: Vec<Tensor<T>>,
}

impl<T: Clone + Default> InferenceSession<T> {
    fn new(model: Model<T>, device: Device) -> Self {
        InferenceSession {
            model,
            device,
            optimized_buffers: Vec::new(),
        }
    }
    
    // 预分配内存缓冲区，避免运行时分配
    fn optimize(&mut self, input_shape: Vec<usize>) {
        println!("为推理预分配内存缓冲区");
        
        // 分析模型计算图，预先分配所有中间张量
        let mut buffer_shapes = Vec::new();
        
        // 简化的内存规划
        for layer_index in 0..self.model.layers.len() {
            // 实际实现会根据层的类型和大小计算缓冲区
            let buffer_shape = match layer_index % 3 {
                0 => vec![input_shape[0], 64],
                1 => vec![input_shape[0], 128],
                _ => vec![input_shape[0], 256],
            };
            
            buffer_shapes.push(buffer_shape);
        }
        
        // 创建优化缓冲区
        for shape in buffer_shapes {
            let buffer = Tensor::new(shape, self.device.clone());
            self.optimized_buffers.push(buffer);
        }
        
        println!("分配了 {} 个优化缓冲区", self.optimized_buffers.len());
    }
    
    // 优化的推理
    fn infer(&mut self, input: Tensor<T>) -> Result<Tensor<T>, &'static str> {
        if self.optimized_buffers.is_empty() {
            return Err("推理会话未优化");
        }
        
        println!("使用预分配缓冲区进行优化推理");
        
        let mut current = input;
        
        // 使用预分配的缓冲区运行每一层
        for (i, layer) in self.model.layers.iter().enumerate() {
            // 在实际实现中，会将结果写入预分配的缓冲区
            // 并重用前一层使用的缓冲区
            let output_buffer = &mut self.optimized_buffers[i];
            
            // 模拟层计算
            current = layer.forward_optimized(&current, output_buffer);
        }
        
        Ok(current)
    }
}

// 3. 分布式训练协调器
struct DistributedTrainer<T> {
    model: Model<T>,
    rank: usize, // 当前进程排名
    world_size: usize, // 总进程数
}

impl<T: Clone + Default> DistributedTrainer<T> {
    fn new(model: Model<T>, rank: usize, world_size: usize) -> Self {
        DistributedTrainer {
            model,
            rank,
            world_size,
        }
    }
    
    // 分片数据集，每个节点拥有部分数据所有权
    fn shard_dataset(&self, dataset: Vec<T>) -> Vec<T> {
        let shard_size = dataset.len() / self.world_size;
        let start = self.rank * shard_size;
        let end = if self.rank == self.world_size - 1 {
            dataset.len() // 最后一个节点可能会多一些数据
        } else {
            (self.rank + 1) * shard_size
        };
        
        dataset[start..end].to_vec()
    }
    
    // 执行分布式训练的一个步骤
    fn train_step(&mut self, local_batch: &[T]) {
        println!("节点 {}/{} 执行训练步骤", self.rank + 1, self.world_size);
        
        // 前向传播
        // 反向传播
        
        // 梯度同步（All-Reduce操作）
        self.sync_gradients();
        
        // 更新模型参数
        self.model.update();
    }
    
    // 同步梯度 - 在真实环境中会涉及网络通信
    fn sync_gradients(&mut self) {
        println!("同步所有节点的梯度");
        // 实际实现中会使用 MPI、NCCL 等库进行梯度通信
    }
}

// 模型定义
struct Model<T> {
    layers: Vec<ModelLayer<T>>,
}

impl<T: Clone + Default> Model<T> {
    fn new() -> Self {
        Model {
            layers: Vec::new(),
        }
    }
    
    fn add_layer(&mut self, layer: ModelLayer<T>) {
        self.layers.push(layer);
    }
    
    fn update(&mut self) {
        for layer in &mut self.layers {
            layer.update();
        }
    }
}

struct ModelLayer<T> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Clone + Default> ModelLayer<T> {
    fn forward_optimized(&self, input: &Tensor<T>, output_buffer: &mut Tensor<T>) -> Tensor<T> {
        // 简化实现
        output_buffer.clone()
    }
    
    fn update(&mut self) {
        // 更新参数
    }
}
```

### 自动微分与所有权转换

所有权系统如何表达和优化自动微分：

1. **所有权驱动的自动微分系统**
   - 基于所有权跟踪的自动微分引擎
   - 通过所有权分析优化内存使用

2. **梯度累积与所有权合并**
   - 所有权合并优化梯度累积
   - 避免不必要的梯度分配

3. **计算图重用策略**
   - 基于所有权的计算图缓存和重用
   - 动态图与静态图的所有权比较

```rust
// 自动微分与所有权示例

// 1. 表达式构建器
enum BinaryOp {
    Add,
    Mul,
    Div,
    Sub,
}

enum UnaryOp {
    Neg,
    Exp,
    Log,
    Relu,
}

// 表达式节点
enum ExprNode<T> {
    Constant(T),
    Variable(usize, T), // 变量ID和值
    BinaryExpr(BinaryOp, Box<ExprNode<T>>, Box<ExprNode<T>>),
    UnaryExpr(UnaryOp, Box<ExprNode<T>>),
}

// 自动微分上下文
struct ADContext<T> {
    variables: Vec<T>,
    gradients: Vec<T>,
    expr_cache: std::collections::HashMap<String, Box<ExprNode<T>>>,
}

impl<T: Clone + Default + std::fmt::Debug> ADContext<T> {
    fn new() -> Self {
        ADContext {
            variables: Vec::new(),
            gradients: Vec::new(),
            expr_cache: std::collections::HashMap::new(),
        }
    }
    
    // 添加变量
    fn add_variable(&mut self, value: T) -> usize {
        let id = self.variables.len();
        self.variables.push(value.clone());
        self.gradients.push(T::default());
        id
    }
    
    // 创建常量表达式
    fn constant(&self, value: T) -> Box<ExprNode<T>> {
        Box::new(ExprNode::Constant(value))
    }
    
    // 创建变量表达式
    fn variable(&self, id: usize) -> Box<ExprNode<T>> {
        Box::new(ExprNode::Variable(id, self.variables[id].clone()))
    }
    
    // 二元操作（消耗输入表达式的所有权）
    fn binary_op(&mut self, op: BinaryOp, left: Box<ExprNode<T>>, right: Box<ExprNode<T>>) -> Box<ExprNode<T>> {
        // 计算缓存键
        let cache_key = format!("{:?}_{:?}_{:?}", op, left, right);
        
        // 检查缓存中是否已有相同表达式
        if let Some(cached) = self.expr_cache.get(&cache_key) {
            println!("重用缓存的表达式");
            return cached.clone();
        }
        
        // 创建新的二元表达式
        let expr = Box::new(ExprNode::BinaryExpr(op, left, right));
        
        // 缓存表达式
        self.expr_cache.insert(cache_key, expr.clone());
        
        expr
    }
    
    // 一元操作
    fn unary_op(&mut self, op: UnaryOp, input: Box<ExprNode<T>>) -> Box<ExprNode<T>> {
        Box::new(ExprNode::UnaryExpr(op, input))
    }
    
    // 计算表达式值
    fn forward(&self, expr: &ExprNode<T>) -> T where T: std::ops::Add<Output = T> + std::ops::Mul<Output = T> {
        match expr {
            ExprNode::Constant(val) => val.clone(),
            ExprNode::Variable(id, _) => self.variables[*id].clone(),
            ExprNode::BinaryExpr(op, left, right) => {
                let left_val = self.forward(left);
                let right_val = self.forward(right);
                
                match op {
                    BinaryOp::Add => left_val + right_val,
                    // 简化实现，其他操作省略
                    _ => T::default(),
                }
            }
            ExprNode::UnaryExpr(op, input) => {
                let input_val = self.forward(input);
                
                match op {
                    // 简化实现
                    _ => T::default(),
                }
            }
        }
    }
    
    // 反向传播计算梯度
    fn backward(&mut self, expr: &ExprNode<T>, grad: T) where T: std::ops::Add<Output = T> {
        match expr {
            ExprNode::Variable(id, _) => {
                // 累积梯度
                // self.gradients[*id] += grad;
            }
            ExprNode::BinaryExpr(op, left, right) => {
                match op {
                    BinaryOp::Add => {
                        // 加法操作梯度简单传递
                        self.backward(left, grad.clone());
                        self.backward(right, grad);
                    }
                    // 其他操作的梯度计算省略
                    _ => {}
                }
            }
            ExprNode::UnaryExpr(op, input) => {
                match op {
                    // 简化实现
                    _ => {}
                }
            }
            _ => {} // 常量不需要梯度
        }
    }
    
    // 获取变量的梯度
    fn get_gradient(&self, id: usize) -> &T {
        &self.gradients[id]
    }
}

// 2. 内存优化的反向传播
struct ReverseMode<T> {
    ops: Vec<Op<T>>,
    variables: Vec<T>,
    gradients: Vec<T>,
}

enum Op<T> {
    // 存储操作类型和相关信息
    AddBackward(usize, usize), // 输出id, 输入id
    MulBackward(usize, usize, T), // 输出id, 输入id, saved_value
    // 其他操作...
}

impl<T: Clone + Default + std::ops::Add<Output = T> + std::ops::Mul<Output = T>> ReverseMode<T> {
    fn new() -> Self {
        ReverseMode {
            ops: Vec::new(),
            variables: Vec::new(),
            gradients: Vec::new(),
        }
    }
    
    // 记录前向操作并构建反向计算图
    fn add(&mut self, a_id: usize, b_id: usize) -> usize {
        // 前向计算
        let a = self.variables[a_id].clone();
        let b = self.variables[b_id].clone();
        let result = a + b;
        
        // 添加结果变量
        let result_id = self.variables.len();
        self.variables.push(result);
        self.gradients.push(T::default());
        
        // 记录反向操作
        self.ops.push(Op::AddBackward(result_id, a_id));
        self.ops.push(Op::AddBackward(result_id, b_id));
        
        result_id
    }
    
    fn mul(&mut self, a_id: usize, b_id: usize) -> usize {
        // 前向计算
        let a = self.variables[a_id].clone();
        let b = self.variables[b_id].clone();
        let result = a.clone() * b.clone();
        
        // 添加结果变量
        let result_id = self.variables.len();
        self.variables.push(result);
        self.gradients.push(T::default());
        
        // 记录反向操作（需要保存前向值用于反向计算）
        self.ops.push(Op::MulBackward(result_id, a_id, b.clone()));
        self.ops.push(Op::MulBackward(result_id, b_id, a));
        
        result_id
    }
    
    // 高效的反向传播
    fn backward(&mut self, output_id: usize) {
        // 初始化输出梯度为1
        self.gradients[output_id] = T::default(); // 应该设为1
        
        // 反向执行操作
        for op in self.ops.iter().rev() {
            match op {
                Op::AddBackward(from_id, to_id) => {
                    // 加法的反向：梯度直接传递
                    let grad = self.gradients[*from_id].clone();
                    // self.gradients[*to_id] += grad;
                }
                Op::MulBackward(from_id, to_id, saved_value) => {
                    // 乘法的反向：梯度乘以另一个输入
                    let grad = self.gradients[*from_id].clone();
                    // self.gradients[*to_id] += grad * saved_value.clone();
                }
                // 其他操作...
            }
        }
    }
    
    // 获取梯度
    fn get_gradient(&self, id: usize) -> &T {
        &self.gradients[id]
    }
}

// 3. 所有权驱动的动态计算图
struct DynamicGraph<T> {
    nodes: Vec<DynamicNode<T>>,
    tape: Vec<usize>, // 记录计算顺序的磁带
}

enum DynamicNode<T> {
    Leaf(T),
    Computed {
        value: T,
        op: DynamicOp,
        inputs: Vec<usize>, // 输入节点索引
    },
}

enum DynamicOp {
    Add,
    Mul,
    Tanh,
    // 其他操作...
}

impl<T: Clone + Default + std::fmt::Debug + std::ops::Add<Output = T> + std::ops::Mul<Output = T>> DynamicGraph<T> {
    fn new() -> Self {
        DynamicGraph {
            nodes: Vec::new(),
            tape: Vec::new(),
        }
    }
    
    // 创建叶节点（拥有数据所有权）
    fn leaf(&mut self, value: T) -> usize {
        let node_id = self.nodes.len();
        self.nodes.push(DynamicNode::Leaf(value));
        node_id
    }
    
    // 创建计算节点
    fn compute(&mut self, op: DynamicOp, inputs: Vec<usize>) -> usize {
        // 获取输入值并执行操作
        let computed_value = self.evaluate_op(&op, &inputs);
        
        // 创建计算节点
        let node_id = self.nodes.len();
        self.nodes.push(DynamicNode::Computed {
            value: computed_value,
            op,
            inputs: inputs.clone(),
        });
        
        // 记录在磁带上，用于反向传播
        self.tape.push(node_id);
        
        node_id
    }
    
    // 根据操作和输入执行计算
    fn evaluate_op(&self, op: &DynamicOp, inputs: &[usize]) -> T {
        match op {
            DynamicOp::Add => {
                if inputs.len() != 2 {
                    panic!("Add 操作需要两个输入");
                }
                self.get_value(inputs[0]).clone() + self.get_value(inputs[1]).clone()
            }
            DynamicOp::Mul => {
                if inputs.len() != 2 {
                    panic!("Mul 操作需要两个输入");
                }
                self.get_value(inputs[0]).clone() * self.get_value(inputs[1]).clone()
            }
            // 其他操作...
            _ => T::default(),
        }
    }
    
    // 获取节点的值
    fn get_value(&self, node_id: usize) -> &T {
        match &self.nodes[node_id] {
            DynamicNode::Leaf(value) => value,
            DynamicNode::Computed { value, .. } => value,
        }
    }
    
    // 反向传播计算梯度
    fn backward(&self, output_id: usize) -> Vec<T> {
        let n = self.nodes.len();
        let mut gradients = vec![T::default(); n];
        
        // 输出节点的梯度初始化为1
        // gradients[output_id] = 1.0;
        
        // 反向遍历磁带
        for &node_id in self.tape.iter().rev() {
            if let DynamicNode::Computed { op, inputs, .. } = &self.nodes[node_id] {
                match op {
                    DynamicOp::Add => {
                        // 加法的梯度直接传递给所有输入
                        for &input_id in inputs {
                            // gradients[input_id] += gradients[node_id].clone();
                        }
                    }
                    DynamicOp::Mul => {
                        // 乘法的梯度需要考虑另一个输入的值
                        if inputs.len() == 2 {
                            let grad = gradients[node_id].clone();
                            // gradients[inputs[0]] += grad.clone() * self.get_value(inputs[1]).clone();
                            // gradients[inputs[1]] += grad * self.get_value(inputs[0]).clone();
                        }
                    }
                    // 其他操作...
                    _ => {},
                }
            }
        }
        
        gradients
    }
    
    // 内存优化策略：释放不再需要的中间节点
    fn optimize_memory(&mut self, keep_nodes: &[usize]) {
        println!("优化计算图内存使用");
        
        // 识别需要保留的节点
        let mut required = vec![false; self.nodes.len()];
        
        // 输出节点必须保留
        for &node_id in keep_nodes {
            required[node_id] = true;
        }
        
        // 反向遍历，标记需要保留的节点
        for &node_id in self.tape.iter().rev() {
            if required[node_id] {
                if let DynamicNode::Computed { inputs, .. } = &self.nodes[node_id] {
                    for &input_id in inputs {
                        required[input_id] = true;
                    }
                }
            }
        }
        
        // 释放不需要的节点内存（实际上我们只能替换，不能真正释放）
        for node_id in 0..self.nodes.len() {
            if !required[node_id] {
                match &mut self.nodes[node_id] {
                    DynamicNode::Computed { value, .. } => {
                        // 在实际应用中可能会使用某种方式回收或最小化此值使用的内存
                        *value = T::default();
                        println!("释放节点 {} 的内存", node_id);
                    }
                    _ => {}
                }
            }
        }
    }
}

// 4. 内联化与优化案例
fn ml_ownership_example() {
    println!("机器学习中的所有权优化示例");
    
    // 创建动态计算图
    let mut graph = DynamicGraph::<f32>::new();
    
    // 创建叶节点
    let x = graph.leaf(2.0);
    let y = graph.leaf(3.0);
    
    // 创建计算
    let z = graph.compute(DynamicOp::Add, vec![x, y]); // z = x + y
    let w = graph.compute(DynamicOp::Mul, vec![z, x]); // w = z * x = (x + y) * x
    
    // 获取计算结果
    println!("计算结果: {:?}", graph.get_value(w));
    
    // 内存优化：只保留需要的节点
    graph.optimize_memory(&[w]);
    
    // 反向传播计算梯度
    let gradients = graph.backward(w);
    
    println!("计算完成");
}
```

## 所有权与图形编程深度探索

### 图形管线资源安全

Rust 所有权如何保障图形管线的资源安全：

1. **GPU 资源生命周期管理**
   - 使用所有权系统管理 GPU 对象生命周期
   - RAII 在图形资源上的安全应用

2. **渲染状态管理的安全保障**
   - 所有权系统保证渲染状态一致性
   - 编译时验证图形 API 使用合法性

3. **命令缓冲区与多线程渲染**
   - 安全的多线程命令缓冲区构建
   - 所有权分割实现并行渲染

```rust
// 图形管线资源安全示例

// 1. GPU 资源抽象
struct GpuDevice {
    device_id: usize,
}

impl GpuDevice {
    fn new() -> Self {
        println!("初始化 GPU 设备");
        GpuDevice { device_id: 1 }
    }
}

// 纹理资源
struct Texture {
    device: std::rc::Rc<GpuDevice>,
    id: usize,
    width: u32,
    height: u32,
    format: TextureFormat,
}

enum TextureFormat {
    RGBA8,
    RGB8,
    Depth32F,
}

impl Texture {
    fn new(device: std::rc::Rc<GpuDevice>, width: u32, height: u32, format: TextureFormat) -> Self {
        println!("创建 {}x{} 纹理", width, height);
        Texture {
            device,
            id: rand::random(),
            width,
            height,
            format,
        }
    }
}

// 资源自动释放
impl Drop for Texture {
    fn drop(&mut self) {
        println!("释放纹理 {} ({}x{})", self.id, self.width, self.height);
    }
}

// 缓冲区资源
struct Buffer {
    device: std::rc::Rc<GpuDevice>,
    id: usize,
    size: usize,
    buffer_type: BufferType,
}

enum BufferType {
    Vertex,
    Index,
    Uniform,
    Storage,
}

impl Buffer {
    fn new(device: std::rc::Rc<GpuDevice>, size: usize, buffer_type: BufferType) -> Self {
        println!("创建 {} 字节 {:?} 缓冲区", size, buffer_type);
        Buffer {
            device,
            id: rand::random(),
            size,
            buffer_type,
        }
    }
    
    // 更新缓冲区内容
    fn update<T>(&mut self, data: &[T]) {
        println!("更新缓冲区 {}", self.id);
    }
}

impl Drop for Buffer {
    fn drop(&mut self) {
        println!("释放缓冲区 {} ({} 字节)", self.id, self.size);
    }
}

// 2. 渲染状态管理
struct RenderState {
    device: std::rc::Rc<GpuDevice>,
    current_pipeline: Option<Pipeline>,
    current_framebuffer: Option<Framebuffer>,
}

impl RenderState {
    fn new(device: std::rc::Rc<GpuDevice>) -> Self {
        RenderState {
            device,
            current_pipeline: None,
            current_framebuffer: None,
        }
    }
    
    // 安全的渲染状态转换
    fn bind_pipeline(&mut self, pipeline: Pipeline) {
        println!("绑定渲染管线 {}", pipeline.id);
        self.current_pipeline = Some(pipeline);
    }
    
    fn bind_framebuffer(&mut self, framebuffer: Framebuffer) {
        println!("绑定帧缓冲区 {}", framebuffer.id);
        self.current_framebuffer = Some(framebuffer);
    }
    
    // 安全的绘制调用 - 编译时检查所有依赖项
    fn draw(&self, vertex_buffer: &Buffer, index_buffer: &Buffer, instance_count: u32) -> Result<(), &'static str> {
        // 检查是否设置了所有必要状态
        if self.current_pipeline.is_none() {
            return Err("未绑定渲染管线");
        }
        
        if self.current_framebuffer.is_none() {
            return Err("未绑定帧缓冲区");
        }
        
        // 检查缓冲区类型
        if matches!(vertex_buffer.buffer_type, BufferType::Vertex) == false {
            return Err("非顶点缓冲区用作顶点数据");
        }
        
        if matches!(index_buffer.buffer_type, BufferType::Index) == false {
            return Err("非索引缓冲区用作索引数据");
        }
        
        println!("安全绘制调用: {} 个实例", instance_count);
        Ok(())
    }
}

// 管线对象
struct Pipeline {
    device: std::rc::Rc<GpuDevice>,
    id: usize,
    shader: Shader,
}

impl Pipeline {
    fn new(device: std::rc::Rc<GpuDevice>, shader: Shader) -> Self {
        println!("创建渲染管线");
        Pipeline {
            device,
            id: rand::random(),
            shader,
        }
    }
}

impl Drop for Pipeline {
    fn drop(&mut self) {
        println!("释放渲染管线 {}", self.id);
    }
}

// 着色器对象
struct Shader {
    device: std::rc::Rc<GpuDevice>,
    id: usize,
}

impl Shader {
    fn new(device: std::rc::Rc<GpuDevice>, vertex_src: &str, fragment_src: &str) -> Self {
        println!("编译着色器");
        Shader {
            device,
            id: rand::random(),
        }
    }
}

impl Drop for Shader {
    fn drop(&mut self) {
        println!("释放着色器 {}", self.id);
    }
}

// 帧缓冲区
struct Framebuffer {
    device: std::rc::Rc<GpuDevice>,
    id: usize,
    color_attachments: Vec<Texture>,
    depth_attachment: Option<Texture>,
}

impl Framebuffer {
    fn new(
        device: std::rc::Rc<GpuDevice>,
        color_attachments: Vec<Texture>,
        depth_attachment: Option<Texture>,
    ) -> Self {
        println!("创建帧缓冲区");
        Framebuffer {
            device,
            id: rand::random(),
            color_attachments,
            depth_attachment,
        }
    }
}

impl Drop for Framebuffer {
    fn drop(&mut self) {
        println!("释放帧缓冲区 {}", self.id);
    }
}

// 3. 命令缓冲区与多线程渲染
struct CommandBuffer {
    device: std::rc::Rc<GpuDevice>,
    id: usize,
    commands: Vec<Command>,
}

enum Command {
    SetPipeline(usize), // Pipeline ID
    SetFramebuffer(usize), // Framebuffer ID
    BindVertexBuffer(usize), // Buffer ID
    BindIndexBuffer(usize), // Buffer ID
    Draw(u32, u32), // 顶点数, 实例数
}

impl CommandBuffer {
    fn new(device: std::rc::Rc<GpuDevice>) -> Self {
        CommandBuffer {
            device,
            id: rand::random(),
            commands: Vec::new(),
        }
    }
    
    // 记录命令
    fn set_pipeline(&mut self, pipeline: &Pipeline) {
        self.commands.push(Command::SetPipeline(pipeline.id));
    }
    
    fn set_framebuffer(&mut self, framebuffer: &Framebuffer) {
        self.commands.push(Command::SetFramebuffer(framebuffer.id));
    }
    
    fn bind_vertex_buffer(&mut self, buffer: &Buffer) {
        if matches!(buffer.buffer_type, BufferType::Vertex) == false {
            panic!("非顶点缓冲区用作顶点数据");
        }
        self.commands.push(Command::BindVertexBuffer(buffer.id));
    }
    
    fn bind_index_buffer(&mut self, buffer: &Buffer) {
        if matches!(buffer.buffer_type, BufferType::Index) == false {
            panic!("非索引缓冲区用作索引数据");
        }
        self.commands.push(Command::BindIndexBuffer(buffer.id));
    }
    
    fn draw(&mut self, vertex_count: u32, instance_count: u32) {
        self.commands.push(Command::Draw(vertex_count, instance_count));
    }
    
    // 提交命令缓冲区执行
    fn submit(self) {
        println!("提交命令缓冲区 {} 执行 ({} 个命令)", self.id, self.commands.len());
        
        // 执行命令
        for cmd in &self.commands {
            match cmd {
                Command::SetPipeline(id) => println!("  设置管线 {}", id),
                Command::SetFramebuffer(id) => println!("  设置帧缓冲区 {}", id),
                Command::BindVertexBuffer(id) => println!("  绑定顶点缓冲区 {}", id),
                Command::BindIndexBuffer(id) => println!("  绑定索引缓冲区 {}", id),
                Command::Draw(vc, ic) => println!("  绘制 {} 个顶点, {} 个实例", vc, ic),
            }
        }
    }
}

impl Drop for CommandBuffer {
    fn drop(&mut self) {
        // 命令缓冲区未提交时输出警告
        if !self.commands.is_empty() {
            println!("警告: 命令缓冲区 {} 被销毁但未提交 ({} 个命令)", self.id, self.commands.len());
        }
    }
}

// 多线程命令缓冲区构建器
struct ParallelCommandBuilder {
    device: std::rc::Rc<GpuDevice>,
}

impl ParallelCommandBuilder {
    fn new(device: std::rc::Rc<GpuDevice>) -> Self {
        ParallelCommandBuilder { device }
    }
    
    // 创建多个命令缓冲区并行构建
    fn build_in_parallel(
        &self,
        render_tasks: Vec<RenderTask>,
    ) -> Vec<CommandBuffer> {
        use std::thread;
        
        let mut handles = Vec::new();
        let device = self.device.clone();
        
        // 每个任务在单独线程中创建命令缓冲区
        for task in render_tasks {
            let task_device = device.clone();
            
            let handle = thread::spawn(move || {
                let mut cmd = CommandBuffer::new(task_device);
                
                // 配置命令缓冲区
                cmd.set_pipeline(&task.pipeline);
                cmd.set_framebuffer(&task.framebuffer);
                cmd.bind_vertex_buffer(&task.vertex_buffer);
                cmd.bind_index_buffer(&task.index_buffer);
                cmd.draw(task.vertex_count, task.instance_count);
                
                cmd
            });
            
            handles.push(handle);
        }
        
        // 收集结果
        let mut command_buffers = Vec::new();
        for handle in handles {
            command_buffers.push(handle.join().unwrap());
        }
        
        command_buffers
    }
}

// 渲染任务描述
struct RenderTask {
    pipeline: Pipeline,
    framebuffer: Framebuffer,
    vertex_buffer: Buffer,
    index_buffer: Buffer,
    vertex_count: u32,
    instance_count: u32,
}

// 使用图形资源示例
fn graphics_resource_example() {
    let device = std::rc::Rc::new(GpuDevice::new());
    
    // 创建资源
    let shader = Shader::new(device.clone(), "顶点着色器源码", "片段着色器源码");
    let pipeline = Pipeline::new(device.clone(), shader);
    
    let color_texture = Texture::new(device.clone(), 1920, 1080, TextureFormat::RGBA8);
    let depth_texture = Texture::new(device.clone(), 1920, 1080, TextureFormat::Depth32F);
    
    let framebuffer = Framebuffer::new(
        device.clone(),
        vec![color_texture],
        Some(depth_texture),
    );
    
    let vertex_buffer = Buffer::new(device.clone(), 1024, BufferType::Vertex);
    let index_buffer = Buffer::new(device.clone(), 512, BufferType::Index);
    
    // 设置渲染状态
    let mut state = RenderState::new(device.clone());
    state.bind_pipeline(pipeline);
    state.bind_framebuffer(framebuffer);
    
    // 执行绘制调用
    if let Err(e) = state.draw(&vertex_buffer, &index_buffer, 1) {
        println!("绘制错误: {}", e);
    }
    
    // 所有资源会在作用域结束时自动释放
}
```

### 场景图所有权层次

所有权系统在场景图结构中的应用：

1. **层次化所有权结构**
   - 场景图的父子关系与所有权层次
   - 组件生命周期与节点生命周期绑定

2. **共享几何体与材质**
   - 使用引用计数共享不可变资源
   - 克隆与引用策略的权衡

3. **场景图遍历与借用**
   - 使用借用系统安全遍历场景图
   - 解决可变性与层次冲突

```rust
// 场景图所有权层次示例

use std::rc::{Rc, Weak};
use std::cell::{RefCell, Ref, RefMut};

// 1. 场景图数据结构
struct SceneNode {
    name: String,
    transform: Transform,
    mesh: Option<Rc<Mesh>>,
    material: Option<Rc<Material>>,
    parent: Option<Weak<RefCell<SceneNode>>>,
    children: Vec<Rc<RefCell<SceneNode>>>,
}

struct Transform {
    position: [f32; 3],
    rotation: [f32; 4],
    scale: [f32; 3],
}

struct Mesh {
    vertices: Vec<[f32; 3]>,
    normals: Vec<[f32; 3]>,
    indices: Vec<u32>,
}

struct Material {
    diffuse_color: [f32; 4],
    specular_color: [f32; 4],
    diffuse_texture: Option<Rc<Texture>>,
}

impl SceneNode {
    fn new(name: &str) -> Self {
        SceneNode {
            name: name.to_string(),
            transform: Transform {
                position: [0.0, 0.0, 0.0],
                rotation: [0.0, 0.0, 0.0, 1.0],
                scale: [1.0, 1.0, 1.0],
            },
            mesh: None,
            material: None,
            parent: None,
            children: Vec::new(),
        }
    }
    
    // 添加子节点，建立所有权关系
    fn add_child(&mut self, child: Rc<RefCell<SceneNode>>) {
        // 更新子节点的父引用（弱引用避免循环）
        child.borrow_mut().parent = Some(Rc::downgrade(&Rc::new(RefCell::new(self.clone()))));
        
        // 添加到子节点列表
        self.children.push(child);
    }
    
    // 移除子节点
    fn remove_child(&mut self, child_name: &str) {
        self.children.retain(|child| {
            let name = &child.borrow().name;
            if name == child_name {
                // 清除父引用
                child.borrow_mut().parent = None;
                false // 从列表中移除
            } else {
                true // 保留在列表中
            }
        });
    }
    
    // 设置网格（共享引用）
    fn set_mesh(&mut self, mesh: Rc<Mesh>) {
        self.mesh = Some(mesh);
    }
    
    // 设置材质（共享引用）
    fn set_material(&mut self, material: Rc<Material>) {
        self.material = Some(material);
    }
    
    // 递归克隆场景子树
    fn clone_subtree(&self) -> SceneNode {
        let mut new_node = SceneNode::new(&self.name);
        new_node.transform = self.transform.clone();
        
        // 共享网格和材质（增加引用计数而非深度复制）
        new_node.mesh = self.mesh.clone();
        new_node.material = self.material.clone();
        
        // 递归克隆子节点
        for child in &self.children {
            let child_clone = Rc::new(RefCell::new(child.borrow().clone_subtree()));
            new_node.add_child(child_clone);
        }
        
        new_node
    }
}

// 支持克隆的类型
impl Clone for SceneNode {
    fn clone(&self) -> Self {
        let mut new_node = SceneNode::new(&self.name);
        new_node.transform = self.transform.clone();
        new_node.mesh = self.mesh.clone();
        new_node.material = self.material.clone();
        // 不复制父子关系
        new_node
    }
}

impl Clone for Transform {
    fn clone(&self) -> Self {
        Transform {
            position: self.position,
            rotation: self.rotation,
            scale: self.scale,
        }
    }
}

// 2. 场景图遍历器
struct SceneVisitor<'a, F>
where
    F: FnMut(&SceneNode),
{
    callback: F,
    _marker: std::marker::PhantomData<&'a ()>,
}

impl<'a, F> SceneVisitor<'a, F>
where
    F: FnMut(&SceneNode),
{
    fn new(callback: F) -> Self {
        SceneVisitor {
            callback,
            _marker: std::marker::PhantomData,
        }
    }
    
    // 借用遍历场景图
    fn visit(&mut self, node: &SceneNode) {
        // 处理当前节点
        (self.callback)(node);
        
        // 递归访问子节点
        for child in &node.children {
            self.visit(&child.borrow());
        }
    }
}

// 可变场景访问器
struct SceneVisitorMut<'a, F>
where
    F: FnMut(&mut SceneNode),
{
    callback: F,
    _marker: std::marker::PhantomData<&'a ()>,
}

impl<'a, F> SceneVisitorMut<'a, F>
where
    F: FnMut(&mut SceneNode),
{
    fn new(callback: F) -> Self {
        SceneVisitorMut {
            callback,
            _marker: std::marker::PhantomData,
        }
    }
    
    // 可变借用遍历场景图
    fn visit(&mut self, node: &mut SceneNode) {
        // 处理当前节点
        (self.callback)(node);
        
        // 递归访问子节点
        // 注意：真实场景中需要额外处理RefCell的可变借用
        for child in &node.children {
            // 这里简化处理，实际需要使用 borrow_mut
            // self.visit(&mut child.borrow_mut());
        }
    }
}

// 3. 场景管理器
struct SceneManager {
    root: Rc<RefCell<SceneNode>>,
    mesh_library: Vec<Rc<Mesh>>,
    material_library: Vec<Rc<Material>>,
    texture_library: Vec<Rc<Texture>>,
}

impl SceneManager {
    fn new() -> Self {
        SceneManager {
            root: Rc::new(RefCell::new(SceneNode::new("root"))),
            mesh_library: Vec::new(),
            material_library: Vec::new(),
            texture_library: Vec::new(),
        }
    }
    
    // 添加共享网格
    fn add_mesh(&mut self, vertices: Vec<[f32; 3]>, normals: Vec<[f32; 3]>, indices: Vec<u32>) -> Rc<Mesh> {
        let mesh = Rc::new(Mesh {
            vertices,
            normals,
            indices,
        });
        
        self.mesh_library.push(mesh.clone());
        mesh
    }
    
    // 添加共享材质
    fn add_material(&mut self, diffuse: [f32; 4], specular: [f32; 4]) -> Rc<Material> {
        let material = Rc::new(Material {
            diffuse_color: diffuse,
            specular_color: specular,
            diffuse_texture: None,
        });
        
        self.material_library.push(material.clone());
        material
    }
    
    // 创建新节点
    fn create_node(&mut self, name: &str, parent: Option<Rc<RefCell<SceneNode>>>) -> Rc<RefCell<SceneNode>> {
        let node = Rc::new(RefCell::new(SceneNode::new(name)));
        
        if let Some(parent_node) = parent {
            parent_node.borrow_mut().add_child(node.clone());
        } else {
            // 没有指定父节点，添加到根节点
            self.root.borrow_mut().add_child(node.clone());
        }
        
        node
    }
    
    // 使用访问器模式访问场景
    fn visit<F>(&self, callback: F)
    where
        F: FnMut(&SceneNode),
    {
        let mut visitor = SceneVisitor::new(callback);
        visitor.visit(&self.root.borrow());
    }
    
    // 取消引用未使用的资源（简化的垃圾收集）
    fn cleanup_unused_resources(&mut self) {
        println!("清理未使用的资源");
        
        // 跟踪已使用的资源
        let mut used_meshes = std::collections::HashSet::new();
        let mut used_materials = std::collections::HashSet::new();
        let mut used_textures = std::collections::HashSet::new();
        
        // 访问场景收集已使用资源
        self.visit(|node| {
            if let Some(mesh) = &node.mesh {
                used_meshes.insert(Rc::as_ptr(mesh));
            }
            
            if let Some(material) = &node.material {
                used_materials.insert(Rc::as_ptr(material));
                
                if let Some(texture) = &material.diffuse_texture {
                    used_textures.insert(Rc::as_ptr(texture));
                }
            }
        });
        
        // 移除未使用的网格
        self.mesh_library.retain(|mesh| {
            let ptr = Rc::as_ptr(mesh);
            used_meshes.contains(&ptr)
        });
        
        // 移除未使用的材质
        self.material_library.retain(|material| {
            let ptr = Rc::as_ptr(material);
            used_materials.contains(&ptr)
        });
        
        // 移除未使用的纹理
        self.texture_library.retain(|texture| {
            let ptr = Rc::as_ptr(texture);
            used_textures.contains(&ptr)
        });
    }
}
```

### 实体组件系统中的所有权深析

所有权系统在实体组件系统 (ECS) 中的应用：

1. **组件存储与所有权模型**
   - 基于所有权的组件存储设计
   - 组件数据的安全访问

2. **系统访问冲突检测**
   - 使用借用规则避免系统间的数据竞争
   - 静态验证系统访问模式

3. **迭代器与零成本抽象**
   - 零开销组件迭代器实现
   - 实体-组件关系的安全表达

```rust
// 实体组件系统中的所有权示例

// 1. ECS 核心类型
type EntityId = usize;

// 组件标记特性
trait Component: 'static {}

// 组件存储
struct ComponentStorage<T: Component> {
    data: Vec<Option<T>>,
}

impl<T: Component> ComponentStorage<T> {
    fn new() -> Self {
        ComponentStorage {
            data: Vec::new(),
        }
    }
    
    // 添加组件
    fn insert(&mut self, entity: EntityId, component: T) {
        // 确保向量足够大
        if entity >= self.data.len() {
            self.data.resize_with(entity + 1, || None);
        }
        
        self.data[entity] = Some(component);
    }
    
    // 获取组件引用
    fn get(&self, entity: EntityId) -> Option<&T> {
        self.data.get(entity)?.as_ref()
    }
    
    // 获取可变组件引用
    fn get_mut(&mut self, entity: EntityId) -> Option<&mut T> {
        self.data.get_mut(entity)?.as_mut()
    }
    
    // 移除组件
    fn remove(&mut self, entity: EntityId) -> Option<T> {
        if entity < self.data.len() {
            self.data[entity].take()
        } else {
            None
        }
    }
}

// 世界管理器
struct World {
    entities: Vec<bool>, // 实体是否活跃
    next_entity: EntityId,
    storages: std::collections::HashMap<std::any::TypeId, Box<dyn std::any::Any>>,
}

impl World {
    fn new() -> Self {
        World {
            entities: Vec::new(),
            next_entity: 0,
            storages: std::collections::HashMap::new(),
        }
    }
    
    // 创建新实体
    fn create_entity(&mut self) -> EntityId {
        let entity = self.next_entity;
        self.next_entity += 1;
        
        if entity >= self.entities.len() {
            self.entities.resize(entity + 1, false);
        }
        
        self.entities[entity] = true;
        entity
    }
    
    // 销毁实体
    fn destroy_entity(&mut self, entity: EntityId) {
        if entity < self.entities.len() {
            self.entities[entity] = false;
            
            // 移除所有组件
            for storage in self.storages.values_mut() {
                // 由于类型擦除，我们需要动态类型转换
                // 在真实实现中，这需要更复杂的处理
            }
        }
    }
    
    // 获取或创建组件存储
    fn get_storage<T: Component>(&mut self) -> &mut ComponentStorage<T> {
        let type_id = std::any::TypeId::of::<ComponentStorage<T>>();
        
        if !self.storages.contains_key(&type_id) {
            let storage = ComponentStorage::<T>::new();
            self.storages.insert(type_id, Box::new(storage));
        }
        
        self.storages
            .get_mut(&type_id)
            .unwrap()
            .downcast_mut::<ComponentStorage<T>>()
            .unwrap()
    }
    
    // 添加组件
    fn add_component<T: Component>(&mut self, entity: EntityId, component: T) {
        let storage = self.get_storage::<T>();
        storage.insert(entity, component);
    }
    
    // 获取组件
    fn get_component<T: Component>(&self, entity: EntityId) -> Option<&T> {
        let type_id = std::any::TypeId::of::<ComponentStorage<T>>();
        let storage = self.storages.get(&type_id)?
            .downcast_ref::<ComponentStorage<T>>()?;
        
        storage.get(entity)
    }
    
    // 获取可变组件
    fn get_component_mut<T: Component>(&mut self, entity: EntityId) -> Option<&mut T> {
        let type_id = std::any::TypeId::of::<ComponentStorage<T>>();
        let storage = self.storages.get_mut(&type_id)?
            .downcast_mut::<ComponentStorage<T>>()?;
        
        storage.get_mut(entity)
    }
}

// 2. 查询与迭代器
struct Query<'a, T: Component> {
    world: &'a World,
    _marker: std::marker::PhantomData<T>,
}

impl<'a, T: Component> Query<'a, T> {
    fn new(world: &'a World) -> Self {
        Query {
            world,
            _marker: std::marker::PhantomData,
        }
    }
    
    // 创建迭代器遍历所有拥有指定组件的实体
    fn iter(&self) -> QueryIterator<'a, T> {
        let type_id = std::any::TypeId::of::<ComponentStorage<T>>();
        
        let storage = self.world.storages.get(&type_id)
            .and_then(|s| s.downcast_ref::<ComponentStorage<T>>());
            
        QueryIterator {
            storage,
            entities: &self.world.entities,
            current_index: 0,
        }
    }
}

// 组件查询迭代器
struct QueryIterator<'a, T: Component> {
    storage: Option<&'a ComponentStorage<T>>,
    entities: &'a [bool],
    current_index: usize,
}

impl<'a, T: Component> Iterator for QueryIterator<'a, T> {
    type Item = (EntityId, &'a T);
    
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(storage) = self.storage {
            while self.current_index < self.entities.len() && self.current_index < storage.data.len() {
                let entity = self.current_index;
                self.current_index += 1;
                
                if self.entities[entity] {
                    if let Some(component) = storage.get(entity) {
                        return Some((entity, component));
                    }
                }
            }
        }
        
        None
    }
}

// 3. 系统与资源访问控制
trait System {
    fn run(&self, world: &mut World);
}

// 标记系统的资源访问模式
struct SystemAccess<R, W> {
    _read: std::marker::PhantomData<R>,
    _write: std::marker::PhantomData<W>,
}

// 示例组件类型
struct Position {
    x: f32,
    y: f32,
}
impl Component for Position {}

struct Velocity {
    x: f32,
    y: f32,
}
impl Component for Velocity {}

struct Health {
    value: i32,
}
impl Component for Health {}

// 物理更新系统（读取 Velocity 写入 Position）
struct PhysicsSystem;

impl System for PhysicsSystem {
    fn run(&self, world: &mut World) {
        // 我们需要分别借用 Position（可变）和 Velocity（不可变）存储
        // 在实际的 ECS 实现中，这可能通过更复杂的机制实现
        
        // 找到所有同时拥有 Position 和 Velocity 的实体
        for entity in 0..world.entities.len() {
            if !world.entities[entity] {
                continue; // 跳过未激活实体
            }
            
            // 同时获取两个组件，一个可变，一个不可变
            if let Some(velocity) = world.get_component::<Velocity>(entity) {
                if let Some(position) = world.get_component_mut::<Position>(entity) {
                    // 更新位置
                    position.x += velocity.x;
                    position.y += velocity.y;
                }
            }
        }
    }
}

// 伤害系统（只写入 Health）
struct DamageSystem {
    damage_amount: i32,
}

impl System for DamageSystem {
    fn run(&self, world: &mut World) {
        // 找到所有拥有 Health 的实体并扣除生命值
        for entity in 0..world.entities.len() {
            if !world.entities[entity] {
                continue;
            }
            
            if let Some(health) = world.get_component_mut::<Health>(entity) {
                health.value -= self.damage_amount;
                
                // 如果生命值归零，销毁实体
                if health.value <= 0 {
                    world.destroy_entity(entity);
                }
            }
        }
    }
}

// 4. 调度器
struct Dispatcher {
    systems: Vec<Box<dyn System>>,
}

impl Dispatcher {
    fn new() -> Self {
        Dispatcher {
            systems: Vec::new(),
        }
    }
    
    // 添加系统
    fn add_system<S: System + 'static>(&mut self, system: S) {
        self.systems.push(Box::new(system));
    }
    
    // 执行所有系统
    fn run_systems(&self, world: &mut World) {
        for system in &self.systems {
            system.run(world);
        }
    }
    
    // 在真实实现中，这里会分析系统间的依赖关系和资源访问冲突
    // 然后并行执行没有冲突的系统
    fn run_systems_parallel(&self, world: &mut World) {
        // 为简化示例，这里只是顺序执行
        self.run_systems(world);
    }
}

// 使用 ECS 示例
fn ecs_ownership_example() {
    // 创建世界
    let mut world = World::new();
    
    // 创建实体和组件
    let entity1 = world.create_entity();
    world.add_component(entity1, Position { x: 0.0, y: 0.0 });
    world.add_component(entity1, Velocity { x: 1.0, y: 0.5 });
    world.add_component(entity1, Health { value: 100 });
    
    let entity2 = world.create_entity();
    world.add_component(entity2, Position { x: 10.0, y: 20.0 });
    world.add_component(entity2, Velocity { x: -0.5, y: 0.0 });
    world.add_component(entity2, Health { value: 50 });
    
    // 创建调度器
    let mut dispatcher = Dispatcher::new();
    dispatcher.add_system(PhysicsSystem);
    dispatcher.add_system(DamageSystem { damage_amount: 10 });
    
    // 运行系统
    println!("运行 ECS 系统");
    dispatcher.run_systems(&mut world);
    
    // 查询结果
    {
        let query = Query::<Position>::new(&world);
        println!("实体位置:");
        for (entity, position) in query.iter() {
            println!("  实体 {}: 位置 ({}, {})", entity, position.x, position.y);
        }
    }
}
```

### 物理与碰撞系统中的借用模型

使用所有权和借用系统解决物理引擎中的安全挑战：

1. **安全碰撞检测**
   - 使用借用分割解决碰撞对的同时访问
   - 所有权系统保证碰撞解算的完整性

2. **物理约束与引用安全**
   - 使用引用实现安全的物理约束
   - 避免约束系统中的循环依赖

3. **动态物理世界**
   - 安全管理动态添加和移除的物理对象
   - 所有权转移模式实现物理交互

```rust
// 物理与碰撞系统中的借用模型示例

// 1. 基础物理对象
struct RigidBody {
    id: usize,
    position: [f32; 3],
    rotation: [f32; 4], // 四元数
    linear_velocity: [f32; 3],
    angular_velocity: [f32; 3],
    inverse_mass: f32,  // 质量的倒数，0 表示静态物体
    restitution: f32,   // 弹性系数
    friction: f32,      // 摩擦系数
}

impl RigidBody {
    fn new(id: usize, mass: f32) -> Self {
        let inverse_mass = if mass > 0.0 { 1.0 / mass } else { 0.0 };
        
        RigidBody {
            id,
            position: [0.0, 0.0, 0.0],
            rotation: [0.0, 0.0, 0.0, 1.0], // 单位四元数
            linear_velocity: [0.0, 0.0, 0.0],
            angular_velocity: [0.0, 0.0, 0.0],
            inverse_mass,
            restitution: 0.5,
            friction: 0.5,
        }
    }
    
    // 应用力
    fn apply_force(&mut self, force: [f32; 3], dt: f32) {
        if self.inverse_mass == 0.0 {
            return; // 静态物体
        }
        
        // F = m*a => a = F/m = F*inverse_mass
        self.linear_velocity[0] += force[0] * self.inverse_mass * dt;
        self.linear_velocity[1] += force[1] * self.inverse_mass * dt;
        self.linear_velocity[2] += force[2] * self.inverse_mass * dt;
    }
    
    // 更新位置
    fn update(&mut self, dt: f32) {
        if self.inverse_mass == 0.0 {
            return; // 静态物体
        }
        
        // 更新位置
        self.position[0] += self.linear_velocity[0] * dt;
        self.position[1] += self.linear_velocity[1] * dt;
        self.position[2] += self.linear_velocity[2] * dt;
        
        // 简化处理：忽略旋转更新
    }
}

// 碰撞形状
enum CollisionShape {
    Sphere { radius: f32 },
    Box { half_extents: [f32; 3] },
}

// 物理对象
struct PhysicsObject {
    body: RigidBody,
    shape: CollisionShape,
    // 其他物理属性
}

// 碰撞信息
struct ContactPoint {
    position: [f32; 3],
    normal: [f32; 3],
    penetration: f32,
}

struct CollisionData {
    body_a_id: usize,
    body_b_id: usize,
    contact_points: Vec<ContactPoint>,
}

// 2. 物理世界
struct PhysicsWorld {
    bodies: Vec<PhysicsObject>,
    gravity: [f32; 3],
    constraints: Vec<Box<dyn Constraint>>,
}

impl PhysicsWorld {
    fn new() -> Self {
        PhysicsWorld {
            bodies: Vec::new(),
            gravity: [0.0, -9.81, 0.0],
            constraints: Vec::new(),
        }
    }
    
    // 添加物理对象
    fn add_object(&mut self, object: PhysicsObject) -> usize {
        let id = object.body.id;
        self.bodies.push(object);
        id
    }
    
    // 添加约束
    fn add_constraint<C: Constraint + 'static>(&mut self, constraint: C) {
        self.constraints.push(Box::new(constraint));
    }
    
    // 更新物理世界
    fn step(&mut self, dt: f32) {
        // 应用重力和其他外力
        for object in &mut self.bodies {
            let mass = if object.body.inverse_mass > 0.0 {
                1.0 / object.body.inverse_mass
            } else {
                0.0
            };
            
            let gravity_force = [
                self.gravity[0] * mass,
                self.gravity[1] * mass,
                self.gravity[2] * mass,
            ];
            
            object.body.apply_force(gravity_force, dt);
        }
        
        // 碰撞检测
        let collisions = self.detect_collisions();
        
        // 解算碰撞约束
        self.resolve_collisions(&collisions, dt);
        
        // 解算约束
        for constraint in &self.constraints {
            constraint.solve(self, dt);
        }
        
        // 更新位置
        for object in &mut self.bodies {
            object.body.update(dt);
        }
    }
    
    // 碰撞检测
    fn detect_collisions(&self) -> Vec<CollisionData> {
        let mut collisions = Vec::new();
        
        // 简单的 O(n²) 碰撞检测
        for i in 0..self.bodies.len() {
            for j in (i+1)..self.bodies.len() {
                if let Some(collision) = self.check_collision(&self.bodies[i], &self.bodies[j]) {
                    collisions.push(collision);
                }
            }
        }
        
        collisions
    }
    
    // 检查两个物体之间的碰撞
    fn check_collision(&self, a: &PhysicsObject, b: &PhysicsObject) -> Option<CollisionData> {
        // 简化实现：只检测球与球的碰撞
        match (&a.shape, &b.shape) {
            (CollisionShape::Sphere { radius: radius_a }, CollisionShape::Sphere { radius: radius_b }) => {
                // 计算球心距离
                let dx = b.body.position[0] - a.body.position[0];
                let dy = b.body.position[1] - a.body.position[1];
                let dz = b.body.position[2] - a.body.position[2];
                
                let distance_squared = dx * dx + dy * dy + dz * dz;
                let combined_radius = radius_a + radius_b;
                
                if distance_squared < combined_radius * combined_radius {
                    // 碰撞发生
                    let distance = distance_squared.sqrt();
                    let penetration = combined_radius - distance;
                    
                    // 归一化碰撞法线
                    let normal = if distance > 0.0001 {
                        [dx / distance, dy / distance, dz / distance]
                    } else {
                        [1.0, 0.0, 0.0] // 任意方向
                    };
                    
                    // 计算碰撞点
                    let collision_point = [
                        a.body.position[0] + normal[0] * radius_a,
                        a.body.position[1] + normal[1] * radius_a,
                        a.body.position[2] + normal[2] * radius_a,
                    ];
                    
                    let contact = ContactPoint {
                        position: collision_point,
                        normal,
                        penetration,
                    };
                    
                    Some(CollisionData {
                        body_a_id: a.body.id,
                        body_b_id: b.body.id,
                        contact_points: vec![contact],
                    })
                } else {
                    None // 没有碰撞
                }
            }
            // 其他形状组合的检测...
            _ => None,
        }
    }
    
    // 解算碰撞
    fn resolve_collisions(&mut self, collisions: &[CollisionData], dt: f32) {
        for collision in collisions {
            // 找到相应的物体
            let (a_index, b_index) = self.find_bodies_by_id(collision.body_a_id, collision.body_b_id);
            
            if let (Some(a_index), Some(b_index)) = (a_index, b_index) {
                // 使用索引分割借用，解决可变引用冲突
                let (first, second) = self.bodies.split_at_mut(std::cmp::max(a_index, b_index));
                
                let a = if a_index < b_index {
                    &mut first[a_index]
                } else {
                    &mut second[0]
                };
                
                let b = if b_index < a_index {
                    &mut first[b_index]
                } else {
                    &mut second[0]
                };
                
                // 对每个接触点应用冲量
                for contact in &collision.contact_points {
                    self.apply_impulse(&mut a.body, &mut b.body, contact, dt);
                }
            }
        }
    }
    
    // 根据 ID 查找物体索引
    fn find_bodies_by_id(&self, id_a: usize, id_b: usize) -> (Option<usize>, Option<usize>) {
        let mut a_index = None;
        let mut b_index = None;
        
        for (i, obj) in self.bodies.iter().enumerate() {
            if obj.body.id == id_a {
                a_index = Some(i);
            } else if obj.body.id == id_b {
                b_index = Some(i);
            }
            
            if a_index.is_some() && b_index.is_some() {
                break;
            }
        }
        
        (a_index, b_index)
    }
    
    // 应用碰撞冲量
    fn apply_impulse(&self, a: &mut RigidBody, b: &mut RigidBody, contact: &ContactPoint, dt: f32) {
        // 相对速度
        let va = a.linear_velocity;
        let vb = b.linear_velocity;
        
        let relative_velocity = [
            vb[0] - va[0],
            vb[1] - va[1],
            vb[2] - va[2],
        ];
        
        // 计算相对速度在碰撞法线方向的分量
        let relative_velocity_along_normal = 
            relative_velocity[0] * contact.normal[0] +
            relative_velocity[1] * contact.normal[1] +
            relative_velocity[2] * contact.normal[2];
        
        // 如果物体已经分离，不应用冲量
        if relative_velocity_along_normal > 0.0 {
            return;
        }
        
        // 计算弹性冲量
        let restitution = a.restitution.min(b.restitution);
        
        // 计算冲量标量
        let j = -(1.0 + restitution) * relative_velocity_along_normal / 
            (a.inverse_mass + b.inverse_mass);
        
        // 应用冲量
        let impulse = [
            contact.normal[0] * j,
            contact.normal[1] * j,
            contact.normal[2] * j,
        ];
        
        // 更新速度
        if a.inverse_mass > 0.0 {
            a.linear_velocity[0] -= impulse[0] * a.inverse_mass;
            a.linear_velocity[1] -= impulse[1] * a.inverse_mass;
            a.linear_velocity[2] -= impulse[2] * a.inverse_mass;
        }
        
        if b.inverse_mass > 0.0 {
            b.linear_velocity[0] += impulse[0] * b.inverse_mass;
            b.linear_velocity[1] += impulse[1] * b.inverse_mass;
            b.linear_velocity[2] += impulse[2] * b.inverse_mass;
        }
        
        // 位置校正（解决重叠）
        let percent = 0.2; // 渗透解决系数
        let slop = 0.01; // 允许的轻微重叠
        
        let correction = if contact.penetration > slop {
            (contact.penetration - slop) * percent / (a.inverse_mass + b.inverse_mass)
        } else {
            0.0
        };
        
        let correction_vector = [
            contact.normal[0] * correction,
            contact.normal[1] * correction,
            contact.normal[2] * correction,
        ];
        
        if a.inverse_mass > 0.0 {
            a.position[0] -= correction_vector[0] * a.inverse_mass;
            a.position[1] -= correction_vector[1] * a.inverse_mass;
            a.position[2] -= correction_vector[2] * a.inverse_mass;
        }
        
        if b.inverse_mass > 0.0 {
            b.position[0] += correction_vector[0] * b.inverse_mass;
            b.position[1] += correction_vector[1] * b.inverse_mass;
            b.position[2] += correction_vector[2] * b.inverse_mass;
        }
    }
    
    // 根据 ID 获取物体引用
    fn get_body(&self, id: usize) -> Option<&PhysicsObject> {
        self.bodies.iter().find(|obj| obj.body.id == id)
    }
    
    // 根据 ID 获取物体可变引用
    fn get_body_mut(&mut self, id: usize) -> Option<&mut PhysicsObject> {
        self.bodies.iter_mut().find(|obj| obj.body.id == id)
    }
}

// 3. 物理约束接口
trait Constraint {
    fn solve(&self, world: &mut PhysicsWorld, dt: f32);
}

// 距离约束（保持两个物体之间的距离）
struct DistanceConstraint {
    body_a_id: usize,
    body_b_id: usize,
    rest_length: f32,
    stiffness: f32,
}

impl Constraint for DistanceConstraint {
    fn solve(&self, world: &mut PhysicsWorld, dt: f32) {
        // 获取两个物体
        let (a_index, b_index) = world.find_bodies_by_id(self.body_a_id, self.body_b_id);
        
        if let (Some(a_index), Some(b_index)) = (a_index, b_index) {
            // 使用分割借用避免可变引用冲突
            let (first, second) = world.bodies.split_at_mut(std::cmp::max(a_index, b_index));
            
            let a = if a_index < b_index {
                &mut first[a_index].body
            } else {
                &mut second[0].body
            };
            
            let b = if b_index < a_index {
                &mut first[b_index].body
            } else {
                &mut second[0].body
            };
            
            // 计算当前距离
            let dx = b.position[0] - a.position[0];
            let dy = b.position[1] - a.position[1];
            let dz = b.position[2] - a.position[2];
            
            let current_length_squared = dx * dx + dy * dy + dz * dz;
            let current_length = current_length_squared.sqrt();
            
            if current_length < 0.0001 {
                // 物体太近，避免除零
                return;
            }
            
            // 计算距离误差
            let error = current_length - self.rest_length;
            
            // 归一化方向向量
            let nx = dx / current_length;
            let ny = dy / current_length;
            let nz = dz / current_length;
            
            // 计算校正强度
            let impulse = error * self.stiffness;
            
            // 应用校正
            if a.inverse_mass > 0.0 {
                a.position[0] += nx * impulse * a.inverse_mass;
                a.position[1] += ny * impulse * a.inverse_mass;
                a.position[2] += nz * impulse * a.inverse_mass;
            }
            
            if b.inverse_mass > 0.0 {
                b.position[0] -= nx * impulse * b.inverse_mass;
                b.position[1] -= ny * impulse * b.inverse_mass;
                b.position[2] -= nz * impulse * b.inverse_mass;
            }
        }
    }
}

// 使用物理系统示例
fn physics_system_example() {
    let mut world = PhysicsWorld::new();
    
    // 创建物理对象
    let ball1 = PhysicsObject {
        body: RigidBody::new(1, 1.0),
        shape: CollisionShape::Sphere { radius: 1.0 },
    };
    
    let mut ball2 = PhysicsObject {
        body: RigidBody::new(2, 1.0),
        shape: CollisionShape::Sphere { radius: 1.0 },
    };
    
    // 设置初始位置
    ball2.body.position = [3.0, 0.0, 0.0];
    
    // 添加到世界
    world.add_object(ball1);
    world.add_object(ball2);
    
    // 添加距离约束
    world.add_constraint(DistanceConstraint {
        body_a_id: 1,
        body_b_id: 2,
        rest_length: 4.0,
        stiffness: 0.1,
    });
    
    // 模拟几个时间步
    println!("开始物理模拟");
    for i in 0..10 {
        world.step(0.016); // 约 60 FPS
        
        // 打印一些物体状态
        if let Some(obj1) = world.get_body(1) {
            println!("步骤 {}: 球 1 位置: {:?}", i, obj1.body.position);
        }
        
        if let Some(obj2) = world.get_body(2) {
            println!("步骤 {}: 球 2 位置: {:?}", i, obj2.body.position);
        }
    }
}
```

## 所有权与形式方法学

### 线性逻辑与所有权深度联系

深入探讨 Rust 所有权系统与线性逻辑的联系：

1. **线性类型理论基础**
   - 线性逻辑如何形式化所有权概念
   - 线性假设与资源使用次数的关系

2. **资源意识计算模型**
   - 线性逻辑与资源意识计算的关系
   - 消耗性资源的形式化模型

3. **所有权模型的证明理论视角**
   - 用证明理论解释 Rust 的借用检查器
   - 建立线性类型系统与 Rust 所有权的同构

```rust
// 线性逻辑与所有权深度联系示例
// (注意：这些示例展示概念，而非实际逻辑系统实现)

// 1. 线性资源类型
// 线性类型保证资源精确使用一次
struct LinearResource {
    data: Vec<u8>,
}

impl LinearResource {
    fn new(size: usize) -> Self {
        println!("创建大小为 {} 的线性资源", size);
        LinearResource {
            data: vec![0; size],
        }
    }
    
    // 消耗资源并返回大小
    fn consume(self) -> usize {
        println!("消耗线性资源");
        self.data.len()
    }
}

// 展示线性逻辑与所有权的关系
fn linear_logic_example() {
    // 创建线性资源
    let resource = LinearResource::new(1024);
    
    // 线性资源只能使用一次
    let size = resource.consume();
    println!("资源大小: {}", size);
    
    // 错误：不能使用已消耗的资源
    // resource.consume(); // 编译错误
    
    // 函数参数中的线性性
    fn process_resource(r: LinearResource) -> usize {
        // 函数获取资源所有权
        r.consume()
    }
    
    let another_resource = LinearResource::new(2048);
    let result = process_resource(another_resource);
    
    // 错误：资源已经被转移并消耗
    // println!("资源数据: {:?}", another_resource.data); // 编译错误
    
    println!("处理结果: {}", result);
}

// 2. 证明理论视角的借用系统
// 通过类型建立公式逻辑与程序的关系

// 线性假设：资源必须精确使用一次
fn linear_assumption_example<T>(resource: T) -> T {
    // 资源作为线性假设传入
    // 必须在函数结束时返回，不能丢弃或复制
    resource
}

// 可克隆类型：允许复制
fn duplicable_assumption_example<T: Clone>(resource: T) -> (T, T) {
    // 可复制类型允许「收缩规则」
    (resource.clone(), resource)
}

// 不可变借用：暂时性的资源访问
fn lending_example<T>(resource: &T) -> &T {
    // 借用对应于临时将资源线性假设转化为指数形式
    // &T 表示 !T (指数形式)
    // 指数形式可以被多次使用
    resource
}

// 可变借用：独占的暂时性资源访问
fn exclusive_lending_example<T>(resource: &mut T) -> &mut T {
    // 可变借用对应于更受限制的指数形式
    // 它保持资源的线性性
    resource
}

// 3. 形式化所有权模型的程序证明
// 通过资源流分析来验证程序的正确性

// 示例：验证资源流
fn verify_resource_flow() {
    // 创建资源
    let resource_a = LinearResource::new(100);
    let resource_b = LinearResource::new(200);
    
    // 验证线性流：每个资源恰好使用一次
    let size_a = resource_a.consume();
    let size_b = resource_b.consume();
    
    // 资源已全部消耗
    println!("总资源大小: {}", size_a + size_b);
}

// 条件资源流：依赖于运行时条件
fn conditional_resource_flow(condition: bool) {
    let resource = LinearResource::new(100);
    
    // 条件分支中的资源消耗
    if condition {
        println!("条件为真，消耗资源");
        resource.consume();
    } else {
        println!("条件为假，以另一种方式消耗资源");
        // 仍然消耗了资源
        let size = resource.consume();
        println!("资源大小: {}", size);
    }
    
    // 无论哪个分支，资源都被消耗了一次
    // 所有权系统通过静态分析确保这一点
}

// 借用检查器作为证明系统
fn borrow_checker_as_proof_system() {
    let mut data = vec![1, 2, 3];
    
    // 创建不可变引用（通过引用规则引入）
    let r1 = &data;
    let r2 = &data;
    
    // 同时存在多个不可变引用是安全的
    println!("r1: {:?}, r2: {:?}", r1, r2);
    
    // 可变引用必须是独占的
    let r3 = &mut data;
    
    // 错误：可变借用与其他借用共存
    // println!("r1: {:?}, r3: {:?}", r1, r3); // 编译错误
    
    // 修改数据
    r3.push(4);
    
    // 借用结束后可以再次访问原始数据
    println!("修改后: {:?}", data);
}
```

### 分离逻辑扩展

分离逻辑如何扩展 Rust 所有权系统：

1. **资源分离原则**
   - 分离逻辑中的资源分区概念
   - 使用分离逻辑表达所有权分割

2. **局部推理与组合性**
   - 分离逻辑支持程序的局部推理
   - 所有权系统的组合性保证

3. **隐式资源规则**
   - 隐式资源模型与显式所有权的关系
   - 分离逻辑框架下的借用

```rust
// 分离逻辑扩展示例

// 1. 资源分离模型
// 分离逻辑核心概念：独立资源可被独立推理

// 数据结构分区示例
struct PartitionedData {
    region_a: Vec<i32>,
    region_b: Vec<i32>,
}

impl PartitionedData {
    fn new() -> Self {
        PartitionedData {
            region_a: vec![1, 2, 3],
            region_b: vec![4, 5, 6],
        }
    }
    
    // 安全并行处理：每个函数只能访问自己的区域
    fn process_regions<FA, FB, RA, RB>(
        &mut self,
        process_a: FA,
        process_b: FB,
    ) -> (RA, RB)
    where
        FA: FnOnce(&mut Vec<i32>) -> RA,
        FB: FnOnce(&mut Vec<i32>) -> RB,
    {
        // 分离逻辑的核心原则：分区资源可以安全并行处理
        let result_a = process_a(&mut self.region_a);
        let result_b = process_b(&mut self.region_b);
        
        (result_a, result_b)
    }
}

// 2. 分离合取操作：分区的形式化表示
fn separation_conjunction_example() {
    let mut data = PartitionedData::new();
    
    // 并行处理两个区域（概念性的分离合取）
    let (sum_a, sum_b) = data.process_regions(
        |region_a| region_a.iter().sum::<i32>(),
        |region_b| region_b.iter().sum::<i32>(),
    );
    
    println!("区域 A 总和: {}, 区域 B 总和: {}", sum_a, sum_b);
    
    // 修改两个区域
    data.process_regions(
        |region_a| region_a.push(10),
        |region_b| region_b.push(20),
    );
    
    println!("修改后：区域 A: {:?}, 区域 B: {:?}", data.region_a, data.region_b);
}

// 3. 局部推理原则
// 可以局部推理一个函数对资源的影响，而不考虑整个程序状态

// 封装与模块化的资源访问
struct ResourceModule<T> {
    state: T,
}

impl<T> ResourceModule<T> {
    fn new(state: T) -> Self {
        ResourceModule { state }
    }
    
    // 以局部方式修改资源
    fn modify<F, R>(&mut self, operation: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        // 封装对资源的访问
        operation(&mut self.state)
    }
    
    // 局部推理：此操作只影响其明确访问的状态
    fn local_reasoning<F, G, R1, R2>(
        module1: &mut ResourceModule<T>,
        module2: &mut ResourceModule<T>,
        op1: F,
        op2: G,
    ) -> (R1, R2)
    where
        F: FnOnce(&mut T) -> R1,
        G: FnOnce(&mut T) -> R2,
    {
        // 分离逻辑的核心：这两个操作可以独立推理
        let result1 = module1.modify(op1);
        let result2 = module2.modify(op2);
        
        (result1, result2)
    }
}

// 4. 隐式共享与分离
fn implicit_sharing_example() {
    let mut data = vec![1, 2, 3, 4, 5];
    
    // 使用分片创建不重叠的部分引用
    let (left, right) = data.split_at_mut(2);
    
    // 这两个引用可以被安全地并行处理
    // 分离逻辑可以证明它们指向不相交的内存区域
    left[0] += 10;
    right[0] *= 2;
    
    println!("处理后的数据: {:?}", data);
    
    // 更复杂的分离：基于索引的访问
    let mut matrix = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
    
    // 可以同时访问不同的行
    let row0 = &mut matrix[0];
    let row2 = &mut matrix[2];
    
    // 分离逻辑保证这些操作互不干扰
    row0[1] = 20;
    row2[1] = 80;
    
    println!("处理后的矩阵: {:?}", matrix);
}

// 5. 框架规则与资源局部性
struct FramedResource {
    core: Vec<i32>,
    metadata: String,
}

impl FramedResource {
    fn new(data: Vec<i32>, meta: &str) -> Self {
        FramedResource {
            core: data,
            metadata: meta.to_string(),
        }
    }
    
    // 框架规则：只操作资源的核心部分，其余保持不变
    fn transform_core<F>(&mut self, operation: F)
    where
        F: FnOnce(&mut Vec<i32>),
    {
        // 操作只影响核心数据，元数据保持不变
        operation(&mut self.core);
        
        // 元数据版本可以自动更新
        self.metadata = format!("{}v2", self.metadata);
    }
}

fn frame_rule_example() {
    let mut resource = FramedResource::new(vec![10, 20, 30], "original-");
    
    // 框架规则：操作只关注它访问的资源部分
    resource.transform_core(|data| {
        data.push(40);
        data.push(50);
    });
    
    println!("转换后的资源: {:?}, 元数据: {}", resource.core, resource.metadata);
    
    // 再次应用框架规则
    resource.transform_core(|data| {
        data.iter_mut().for_each(|x| *x *= 2);
    });
    
    println!("再次转换后: {:?}, 元数据: {}", resource.core, resource.metadata);
}
```

### 程序验证与所有权证明

程序验证如何与所有权系统结合：

1. **所有权不变量验证**
   - 使用程序验证工具证明所有权规则遵循
   - 扩展验证到资源安全属性

2. **借用检查器的形式化验证**
   - 验证借用检查器自身的正确性
   - 形式化借用规则的完备性

3. **所有权与程序规约**
   - 使用所有权信息简化程序验证
   - 所有权驱动的契约验证

```rust
// 程序验证与所有权证明示例

// 1. 所有权不变量验证模型
struct VerifiedResource {
    data: Vec<u8>,
    is_initialized: bool,
}

impl VerifiedResource {
    // 不变量：资源必须先初始化，后使用
    fn new() -> Self {
        VerifiedResource {
            data: Vec::new(),
            is_initialized: false,
        }
    }
    
    // 初始化资源
    fn initialize(&mut self, size: usize) {
        // 前置条件：资源未初始化
        assert!(!self.is_initialized, "资源已经初始化");
        
        self.data = vec![0; size];
        self.is_initialized = true;
        
        // 后置条件：资源现在已初始化
        assert!(self.is_initialized, "初始化失败");
    }
    
    // 使用资源
    fn use_resource(&self) -> usize {
        // 前置条件：资源必须已初始化
        assert!(self.is_initialized, "使用未初始化的资源");
        
        self.data.len()
    }
    
    // 可变使用资源
    fn modify_resource(&mut self, index: usize, value: u8) {
        // 前置条件：资源必须已初始化且索引有效
        assert!(self.is_initialized, "修改未初始化的资源");
        assert!(index < self.data.len(), "索引超出范围");
        
        self.data[index] = value;
        
        // 后置条件：数据已更新
        assert_eq!(self.data[index], value, "数据更新失败");
    }
}

// 2. 使用验证属性模拟形式化验证
#[derive(Debug)]
enum VerificationResult {
    Success,
    Failure(String),
}

// 模拟形式化验证工具
struct Verifier;

impl Verifier {
    // 验证资源使用的安全性
    fn verify_resource_usage(code: &str) -> VerificationResult {
        println!("验证代码: {}", code);
        
        // 模拟静态分析过程
        if code.contains("use_resource") && !code.contains("initialize") {
            return VerificationResult::Failure(
                "潜在错误：可能在初始化前使用资源".to_string()
            );
        }
        
        if code.contains("modify_resource") && code.contains("index > 10") {
            return VerificationResult::Failure(
                "潜在错误：可能的索引越界访问".to_string()
            );
        }
        
        VerificationResult::Success
    }
    
    // 验证引用的安全性
    fn verify_references(code: &str) -> VerificationResult {
        println!("验证引用安全性: {}", code);
        
        // 模拟借用检查器
        if code.contains("&mut") && code.contains("multiple") {
            return VerificationResult::Failure(
                "潜在错误：可能存在多个可变引用".to_string()
            );
        }
        
        if code.contains("&") && code.contains("&mut") && code.contains("simultaneous") {
            return VerificationResult::Failure(
                "潜在错误：可能同时存在可变引用和不可变引用".to_string()
            );
        }
        
        VerificationResult::Success
    }
    
    // 验证不变量
    fn verify_invariants<T, F>(check_fn: F) -> VerificationResult 
    where
        F: FnOnce() -> Result<T, String>,
    {
        match check_fn() {
            Ok(_) => VerificationResult::Success,
            Err(msg) => VerificationResult::Failure(msg),
        }
    }
}

// 3. 验证驱动的所有权模式
fn ownership_verification_example() {
    // 验证资源使用
    let resource_code = "
        let mut res = VerifiedResource::new();
        res.use_resource(); // 未初始化就使用
    ";
    
    let result = Verifier::verify_resource_usage(resource_code);
    println!("资源使用验证结果: {:?}", result);
    
    // 验证引用安全
    let ref_code = "
        let mut data = vec![1, 2, 3];
        let r1 = &mut data; // 创建可变引用
        let r2 = &mut data; // multiple 可变引用
        *r1 = vec![4, 5, 6];
    ";
    
    let result = Verifier::verify_references(ref_code);
    println!("引用安全验证结果: {:?}", result);
    
    // 验证不变量
    let result = Verifier::verify_invariants(|| {
        let mut resource = VerifiedResource::new();
        
        // 检查初始化-使用顺序
        if true {
            resource.initialize(10);
            resource.use_resource(); // 正确顺序
            Ok(())
        } else {
            // 这个分支会导致错误
            resource.use_resource(); // 未初始化使用
            resource.initialize(10);
            Err("违反了资源使用不变量".to_string())
        }
    });
    
    println!("不变量验证结果: {:?}", result);
}

// 4. 基于所有权的契约
trait ResourceContract {
    // 前置条件：资源必须满足什么条件
    fn precondition(&self) -> bool;
    
    // 后置条件：操作后资源必须满足什么条件
    fn postcondition(&self) -> bool;
    
    // 不变量：资源在任何情况下都必须满足的条件
    fn invariant(&self) -> bool;
}

struct VerifiedVector {
    data: Vec<i32>,
    sorted: bool,
}

impl VerifiedVector {
    fn new() -> Self {
        VerifiedVector {
            data: Vec::new(),
            sorted: true, // 空向量视为已排序
        }
    }
    
    // 添加元素，可能破坏排序
    fn push(&mut self, value: i32) {
        self.data.push(value);
        
        // 检查是否仍然有序
        if !self.data.is_empty() && self.data.len() > 1 {
            let last_idx = self.data.len() - 1;
            self.sorted = self.data[last_idx - 1] <= self.data[last_idx];
        }
    }
    
    // 排序向量
    fn sort(&mut self) {
        self.data.sort();
        self.sorted = true;
    }
    
    // 要求向量已排序的操作
    fn binary_search(&self, target: i32) -> Option<usize> {
        // 契约：必须在排序状态下调用
        assert!(self.sorted, "在未排序向量上执行二分搜索");
        
        // 二分查找实现
        self.data.binary_search(&target).ok()
    }
}

impl ResourceContract for VerifiedVector {
    fn precondition(&self) -> bool {
        // 通用前置条件：向量存在
        true
    }
    
    fn postcondition(&self) -> bool {
        // 通用后置条件：状态一致性
        if self.sorted {
            // 如果声称已排序，则验证是否真的有序
            self.data.windows(2).all(|w| w[0] <= w[1])
        } else {
            true
        }
    }
    
    fn invariant(&self) -> bool {
        // 不变量：sorted 标志必须正确反映向量排序状态
        let actually_sorted = self.data.is_empty() || 
            self.data.windows(2).all(|w| w[0] <= w[1]);
            
        self.sorted == actually_sorted
    }
}

// 使用契约验证
fn contract_verification_example() {
    let mut v = VerifiedVector::new();
    
    // 添加元素
    v.push(5);
    v.push(2);
    v.push(8);
    
    // 验证不变量
    assert!(v.invariant(), "不变量被破坏");
    
    // 尝试在未排序状态下进行二分搜索
    if v.sorted {
        let result = v.binary_search(5);
        println!("搜索结果: {:?}", result);
    } else {
        println!("向量未排序，先排序");
        v.sort();
        
        // 排序后验证不变量
        assert!(v.invariant(), "排序后不变量被破坏");
        
        let result = v.binary_search(5);
        println!("搜索结果: {:?}", result);
    }
}
```

### 智能合约与所有权安全

所有权系统在智能合约领域的应用：

1. **代币与资源所有权**
   - 使用所有权系统实现安全代币模型
   - 所有权转移作为交易机制

2. **合约状态安全**
   - 所有权保证的合约状态一致性
   - 基于类型的状态机实现

3. **资产安全与访问控制**
   - 类型级别的资产所有权保证
   - 所有权分离的多签安全

```rust
// 智能合约与所有权安全示例

// 1. 代币模型与所有权
struct Token {
    id: u64,
    value: u128,
}

struct TokenAccount {
    owner: Address,
    tokens: Vec<Token>,
    balance: u128,
}

#[derive(Clone, PartialEq)]
struct Address([u8; 32]);

impl Address {
    fn new() -> Self {
        Address([0; 32]) // 简化示例，实际上应该是加密生成的
    }
}

// 代币转移操作
enum TransferResult {
    Success,
    InsufficientFunds,
    Unauthorized,
}

struct TokenContract {
    accounts: std::collections::HashMap<Address, TokenAccount>,
    next_token_id: u64,
}

impl TokenContract {
    fn new() -> Self {
        TokenContract {
            accounts: std::collections::HashMap::new(),
            next_token_id: 1,
        }
    }
    
    // 创建账户
    fn create_account(&mut self, owner: Address) {
        if !self.accounts.contains_key(&owner) {
            self.accounts.insert(owner.clone(), TokenAccount {
                owner,
                tokens: Vec::new(),
                balance: 0,
            });
        }
    }
    
    // 铸造代币（创建新代币并分配给账户）
    fn mint(&mut self, to: &Address, value: u128) {
        if !self.accounts.contains_key(to) {
            self.create_account(to.clone());
        }
        
        let token = Token {
            id: self.next_token_id,
            value,
        };
        
        self.next_token_id += 1;
        
        if let Some(account) = self.accounts.get_mut(to) {
            account.tokens.push(token);
            account.balance += value;
        }
    }
    
    // 转移代币（所有权转移）
    fn transfer(&mut self, from: &Address, to: &Address, amount: u128) -> TransferResult {
        // 检查发送方账户是否存在且余额充足
        let from_account = match self.accounts.get_mut(from) {
            Some(account) => account,
            None => return TransferResult::Unauthorized,
        };
        
        if from_account.balance < amount {
            return TransferResult::InsufficientFunds;
        }
        
        // 确保接收方账户存在
        if !self.accounts.contains_key(to) {
            self.create_account(to.clone());
        }
        
        // 执行转账（转移所有权）
        let mut remaining = amount;
        let mut tokens_to_transfer = Vec::new();
        
        // 收集要转移的代币
        for i in (0..from_account.tokens.len()).rev() {
            if remaining == 0 {
                break;
            }
            
            let token = &from_account.tokens[i];
            let transfer_amount = std::cmp::min(token.value, remaining);
            
            if transfer_amount == token.value {
                // 完全转移令牌
                let token = from_account.tokens.remove(i);
                tokens_to_transfer.push(token);
                remaining -= transfer_amount;
            } else {
                // 部分转移令牌（拆分）
                from_account.tokens[i].value -= transfer_amount;
                tokens_to_transfer.push(Token {
                    id: self.next_token_id,
                    value: transfer_amount,
                });
                self.next_token_id += 1;
                remaining -= transfer_amount;
            }
        }
        
        // 更新发送方余额
        from_account.balance -= amount;
        
        // 更新接收方账户
        if let Some(to_account) = self.accounts.get_mut(to) {
            to_account.tokens.extend(tokens_to_transfer);
            to_account.balance += amount;
        }
        
        TransferResult::Success
    }
    
    // 查询余额
    fn balance_of(&self, owner: &Address) -> u128 {
        self.accounts.get(owner).map_or(0, |account| account.balance)
    }
}

// 2. 基于类型状态的合约安全
// 使用类型状态模式确保合约状态转换的安全性

// 合约状态标记
struct Created;
struct Running;
struct Paused;
struct Terminated;

// 参数化状态的合约
struct StatefulContract<State> {
    balance: u128,
    owner: Address,
    _state: std::marker::PhantomData<State>,
}

// 创建状态的实现
impl StatefulContract<Created> {
    fn new(owner: Address) -> Self {
        StatefulContract {
            balance: 0,
            owner,
            _state: std::marker::PhantomData,
        }
    }
    
    // 启动合约，转换到运行状态
    fn start(self) -> StatefulContract<Running> {
        println!("合约启动");
        StatefulContract {
            balance: self.balance,
            owner: self.owner,
            _state: std::marker::PhantomData,
        }
    }
}

// 运行状态的实现
impl StatefulContract<Running> {
    // 运行状态可以接收资金
    fn deposit(&mut self, amount: u128) {
        self.balance += amount;
        println!("存入 {} 单位，新余额: {}", amount, self.balance);
    }
    
    // 运行状态可以支付
    fn withdraw(&mut self, amount: u128) -> Result<(), &'static str> {
        if amount > self.balance {
            return Err("余额不足");
        }
        
        self.balance -= amount;
        println!("提取 {} 单位，新余额: {}", amount, self.balance);
        Ok(())
    }
    
    // 暂停合约
    fn pause(self) -> StatefulContract<Paused> {
        println!("合约暂停");
        StatefulContract {
            balance: self.balance,
            owner: self.owner,
            _state: std::marker::PhantomData,
        }
    }
    
    // 终止合约
    fn terminate(self) -> StatefulContract<Terminated> {
        println!("合约终止");
        StatefulContract {
            balance: self.balance,
            owner: self.owner,
            _state: std::marker::PhantomData,
        }
    }
}

// 暂停状态的实现
impl StatefulContract<Paused> {
    // 恢复合约运行
    fn resume(self) -> StatefulContract<Running> {
        println!("合约恢复运行");
        StatefulContract {
            balance: self.balance,
            owner: self.owner,
            _state: std::marker::PhantomData,
        }
    }
    
    // 终止合约
    fn terminate(self) -> StatefulContract<Terminated> {
        println!("合约终止");
        StatefulContract {
            balance: self.balance,
            owner: self.owner,
            _state: std::marker::PhantomData,
        }
    }
}

// 终止状态的实现
impl StatefulContract<Terminated> {
    // 提取所有剩余资金
    fn withdraw_all(self) -> u128 {
        println!("提取所有剩余资金: {}", self.balance);
        self.balance
    }
}

// 3. 多签资产保护
struct MultiSigWallet {
    owners: Vec<Address>,
    required_confirmations: usize,
    transactions: Vec<Transaction>,
}

struct Transaction {
    id: u64,
    to: Address,
    amount: u128,
    confirmations: Vec<Address>,
    executed: bool,
}

impl MultiSigWallet {
    fn new(owners: Vec<Address>, required: usize) -> Self {
        assert!(!owners.is_empty(), "所有者不能为空");
        assert!(required > 0 && required <= owners.len(), "确认数要求无效");
        
        MultiSigWallet {
            owners,
            required_confirmations: required,
            transactions: Vec::new(),
        }
    }
    
    // 提交交易
    fn submit_transaction(&mut self, sender: &Address, to: Address, amount: u128) -> Result<u64, &'static str> {
        // 验证发送者是否为所有者
        if !self.owners.contains(sender) {
            return Err("只有所有者可以提交交易");
        }
        
        let tx_id = self.transactions.len() as u64;
        
        let transaction = Transaction {
            id: tx_id,
            to,
            amount,
            confirmations: vec![sender.clone()], // 自动确认
            executed: false,
        };
        
        self.transactions.push(transaction);
        
        println!("交易 {} 已提交并得到 1 次确认", tx_id);
        
        // 如果只需要一个确认，立即执行
        if self.required_confirmations == 1 {
            self.execute_transaction(tx_id)?;
        }
        
        Ok(tx_id)
    }
    
    // 确认交易
    fn confirm_transaction(&mut self, owner: &Address, tx_id: u64) -> Result<(), &'static str> {
        // 验证所有者
        if !self.owners.contains(owner) {
            return Err("只有所有者可以确认交易");
        }
        
        // 获取交易
        let tx = self.transactions.get_mut(tx_id as usize)
            .ok_or("交易不存在")?;
            
        // 检查交易是否已执行
        if tx.executed {
            return Err("交易已执行");
        }
        
        // 检查是否已确认
        if tx.confirmations.contains(owner) {
            return Err("交易已经被此所有者确认");
        }
        
        // 添加确认
        tx.confirmations.push(owner.clone());
        println!("交易 {} 得到新确认，当前 {}/{} 确认", 
            tx_id, tx.confirmations.len(), self.required_confirmations);
        
        // 检查是否有足够确认
        if tx.confirmations.len() >= self.required_confirmations {
            self.execute_transaction(tx_id)?;
        }
        
        Ok(())
    }
    
    // 执行交易
    fn execute_transaction(&mut self, tx_id: u64) -> Result<(), &'static str> {
        // 获取交易
        let tx = self.transactions.get_mut(tx_id as usize)
            .ok_or("交易不存在")?;
            
        // 检查交易状态
        if tx.executed {
            return Err("交易已执行");
        }
        
        if tx.confirmations.len() < self.required_confirmations {
            return Err("确认数不足");
        }
        
        // 执行交易（在实际场景中，这里会调用转账函数）
        tx.executed = true;
        
        println!("交易 {} 执行成功：转移 {} 单位到 {:?}", 
            tx_id, tx.amount, tx.to);
            
        Ok(())
    }
}

// 智能合约示例
fn smart_contract_example() {
    // 1. 代币合约示例
    let mut token_contract = TokenContract::new();
    
    let alice = Address::new();
    let bob = Address::new();
    
    // 铸造代币
    token_contract.mint(&alice, 1000);
    println!("Alice 余额: {}", token_contract.balance_of(&alice));
    
    // 转移代币
    match token_contract.transfer(&alice, &bob, 300) {
        TransferResult::Success => println!("转账成功"),
        TransferResult::InsufficientFunds => println!("余额不足"),
        TransferResult::Unauthorized => println!("未授权"),
    }
    
    println!("转账后 Alice 余额: {}", token_contract.balance_of(&alice));
    println!("转账后 Bob 余额: {}", token_contract.balance_of(&bob));
    
    // 2. 类型状态合约示例
    let owner = Address::new();
    let contract = StatefulContract::<Created>::new(owner);
    
    // 启动合约
    let mut running_contract = contract.start();
    
    // 存入和提取资金
    running_contract.deposit(500);
    let _ = running_contract.withdraw(200);
    
    // 暂停合约
    let paused_contract = running_contract.pause();
    
    // 恢复合约
    let mut running_again = paused_contract.resume();
    
    running_again.deposit(300);
    
    // 终止合约
    let terminated = running_again.terminate();
    
    // 提取所有资金
    let final_balance = terminated.withdraw_all();
    println!("最终提取: {}", final_balance);
    
    // 3. 多签钱包示例
    let owner1 = Address::new();
    let owner2 = Address::new();
    let owner3 = Address::new();
    
    let mut wallet = MultiSigWallet::new(
        vec![owner1.clone(), owner2.clone(), owner3.clone()],
        2 // 需要2个确认
    );
    
    // 提交交易
    let dest = Address::new();
    let tx_id = wallet.submit_transaction(&owner1, dest.clone(), 1000).unwrap();
    
    // 确认交易
    let _ = wallet.confirm_transaction(&owner2, tx_id);
    
    // 现在交易应该已执行，因为有两个确认
    println!("多签交易示例完成");
}
```

## 操作系统与所有权系统

### 内核资源管理

操作系统内核如何利用所有权系统进行资源管理：

1. **内核资源安全**
   - 内核级资源的安全管理
   - 所有权系统防止内核漏洞

2. **零成本资源追踪**
   - 编译时资源验证取代运行时检查
   - 减少内核中的检查开销

3. **内核对象生命周期**
   - 安全管理内核对象的生命周期
   - 所有权转移作为内核调用语义

```rust
// 内核资源管理示例

// 1. 内核级资源抽象
struct KernelResource {
    handle: u64,
    resource_type: ResourceType,
}

enum ResourceType {
    Memory,
    File,
    Socket,
    Process,
}

// 内核操作结果
type KernelResult<T> = Result<T, KernelError>;

#[derive(Debug)]
enum KernelError {
    InvalidResource,
    AccessDenied,
    ResourceExhausted,
    InvalidOperation,
}

// 内核级别的资源管理器
struct KernelResourceManager {
    next_handle: u64,
    active_resources: std::collections::HashMap<u64, ResourceType>,
}

impl KernelResourceManager {
    fn new() -> Self {
        KernelResourceManager {
            next_handle: 1,
            active_resources: std::collections::HashMap::new(),
        }
    }
    
    // 分配新资源
    fn allocate(&mut self, res_type: ResourceType) -> KernelResource {
        let handle = self.next_handle;
        self.next_handle += 1;
        
        self.active_resources.insert(handle, res_type.clone());
        
        println!("内核：分配 {:?} 资源，句柄 {}", res_type, handle);
        
        KernelResource {
            handle,
            resource_type: res_type,
        }
    }
    
    // 释放资源
    fn release(&mut self, resource: KernelResource) {
        if let Some(res_type) = self.active_resources.remove(&resource.handle) {
            println!("内核：释放 {:?} 资源，句柄 {}", res_type, resource.handle);
        } else {
            println!("警告：尝试释放不存在的资源 {}", resource.handle);
        }
    }
    
    // 验证资源是否有效
    fn validate(&self, resource: &KernelResource) -> bool {
        if let Some(stored_type) = self.active_resources.get(&resource.handle) {
            &resource.resource_type == stored_type
        } else {
            false
        }
    }
}

// 2. 内核内存管理
struct KernelMemory {
    resource: KernelResource,
    size: usize,
    permissions: MemoryPermissions,
}

struct MemoryPermissions {
    read: bool,
    write: bool,
    execute: bool,
}

// 内存管理器
struct MemoryManager<'a> {
    kernel: &'a mut KernelResourceManager,
}

impl<'a> MemoryManager<'a> {
    fn new(kernel: &'a mut KernelResourceManager) -> Self {
        MemoryManager { kernel }
    }
    
    // 分配内存
    fn allocate(&mut self, size: usize, perms: MemoryPermissions) -> KernelResult<KernelMemory> {
        if size == 0 {
            return Err(KernelError::InvalidOperation);
        }
        
        // 分配内核资源
        let resource = self.kernel.allocate(ResourceType::Memory);
        
        Ok(KernelMemory {
            resource,
            size,
            permissions: perms,
        })
    }
    
    // 重新分配内存（所有权转移）
    fn reallocate(&mut self, memory: KernelMemory, new_size: usize) -> KernelResult<KernelMemory> {
        // 验证内存资源
        if !self.kernel.validate(&memory.resource) {
            return Err(KernelError::InvalidResource);
        }
        
        println!("内核：重新分配内存从 {} 到 {} 字节", memory.size, new_size);
        
        // 创建新内存对象
        let new_memory = KernelMemory {
            resource: memory.resource, // 重用原始句柄
            size: new_size,
            permissions: memory.permissions,
        };
        
        Ok(new_memory)
    }
}

// 3. 文件系统资源
struct KernelFile {
    resource: KernelResource,
    path: String,
    mode: FileMode,
}

enum FileMode {
    Read,
    Write,
    ReadWrite,
}

// 文件系统管理器
struct FileManager<'a> {
    kernel: &'a mut KernelResourceManager,
}

impl<'a> FileManager<'a> {
    fn new(kernel: &'a mut KernelResourceManager) -> Self {
        FileManager { kernel }
    }
    
    // 打开文件
    fn open(&mut self, path: &str, mode: FileMode) -> KernelResult<KernelFile> {
        // 分配文件资源
        let resource = self.kernel.allocate(ResourceType::File);
        
        println!("内核：打开文件 '{}'", path);
        
        Ok(KernelFile {
            resource,
            path: path.to_string(),
            mode,
        })
    }
    
    // 读取文件
    fn read(&self, file: &KernelFile, buffer: &mut [u8]) -> KernelResult<usize> {
        // 验证文件资源
        if !self.kernel.validate(&file.resource) {
            return Err(KernelError::InvalidResource);
        }
        
        // 检查读取权限
        match file.mode {
            FileMode::Read | FileMode::ReadWrite => {},
            _ => return Err(KernelError::AccessDenied),
        }
        
        // 模拟读取操作
        let read_size = std::cmp::min(buffer.len(), 100);
        println!("内核：从 '{}' 读取 {} 字节", file.path, read_size);
        
        Ok(read_size)
    }
    
    // 写入文件
    fn write(&self, file: &KernelFile, buffer: &[u8]) -> KernelResult<usize> {
        // 验证文件资源
        if !self.kernel.validate(&file.resource) {
            return Err(KernelError::InvalidResource);
        }
        
        // 检查写入权限
        match file.mode {
            FileMode::Write | FileMode::ReadWrite => {},
            _ => return Err(KernelError::AccessDenied),
        }
        
        // 模拟写入操作
        println!("内核：向 '{}' 写入 {} 字节", file.path, buffer.len());
        
        Ok(buffer.len())
    }
    
    // 关闭文件（消耗文件所有权）
    fn close(&mut self, file: KernelFile) {
        // 释放资源
        self.kernel.release(file.resource);
        println!("内核：关闭文件 '{}'", file.path);
    }
}

// 4. 进程资源
struct KernelProcess {
    resource: KernelResource,
    pid: u32,
    state: ProcessState,
}

enum ProcessState {
    Created,
    Running,
    Suspended,
    Terminated,
}

// 进程管理器
struct ProcessManager<'a> {
    kernel: &'a mut KernelResourceManager,
    next_pid: u32,
}

impl<'a> ProcessManager<'a> {
    fn new(kernel: &'a mut KernelResourceManager) -> Self {
        ProcessManager { 
            kernel,
            next_pid: 1,
        }
    }
    
    // 创建进程
    fn create_process(&mut self) -> KernelProcess {
        let pid = self.next_pid;
        self.next_pid += 1;
        
        let resource = self.kernel.allocate(ResourceType::Process);
        println!("内核：创建进程 PID {}", pid);
        
        KernelProcess {
            resource,
            pid,
            state: ProcessState::Created,
        }
    }
    
    // 启动进程
    fn start_process(&mut self, mut process: KernelProcess) -> KernelResult<KernelProcess> {
        // 验证进程资源
        if !self.kernel.validate(&process.resource) {
            return Err(KernelError::InvalidResource);
        }
        
        match process.state {
            ProcessState::Created | ProcessState::Suspended => {
                println!("内核：启动进程 PID {}", process.pid);
                process.state = ProcessState::Running;
                Ok(process)
            }
            ProcessState::Running => {
                println!("警告：进程 PID {} 已在运行", process.pid);
                Ok(process)
            }
            ProcessState::Terminated => {
                Err(KernelError::InvalidOperation)
            }
        }
    }
    
    // 挂起进程
    fn suspend_process(&mut self, mut process: KernelProcess) -> KernelResult<KernelProcess> {
        // 验证进程资源
        if !self.kernel.validate(&process.resource) {
            return Err(KernelError::InvalidResource);
        }
        
        if process.state == ProcessState::Running {
            println!("内核：挂起进程 PID {}", process.pid);
            process.state = ProcessState::Suspended;
            Ok(process)
        } else {
            Err(KernelError::InvalidOperation)
        }
    }
    
    // 终止进程
    fn terminate_process(&mut self, mut process: KernelProcess) -> KernelProcess {
        if process.state != ProcessState::Terminated {
            println!("内核：终止进程 PID {}", process.pid);
            process.state = ProcessState::Terminated;
        }
        
        process
    }
    
    // 回收进程资源（消耗进程所有权）
    fn reap_process(&mut self, process: KernelProcess) {
        if process.state == ProcessState::Terminated {
            println!("内核：回收进程 PID {}", process.pid);
            self.kernel.release(process.resource);
        } else {
            println!("警告：尝试回收未终止的进程 PID {}", process.pid);
        }
    }
}

// 内核资源管理演示
fn kernel_resource_example() {
    // 创建内核资源管理器
    let mut kernel = KernelResourceManager::new();
    
    // 内存管理示例
    {
        let mut memory_mgr = MemoryManager::new(&mut kernel);
        
        // 分配内存
        let memory = memory_mgr.allocate(
            4096,
            MemoryPermissions { read: true, write: true, execute: false }
        ).unwrap();
        
        println!("应用：分配了 {} 字节的内存，句柄 {}", memory.size, memory.resource.handle);
        
        // 重新分配内存
        let larger_memory = memory_mgr.reallocate(memory, 8192).unwrap();
        
        println!("应用：重新分配到 {} 字节的内存", larger_memory.size);
        
        // 内存在作用域结束时会自动释放
        // 但在真实内核中，我们需要显式释放
        kernel.release(larger_memory.resource);
    }
    
    // 文件系统示例
    {
        let mut file_mgr = FileManager::new(&mut kernel);
        
        // 打开文件
        let file = file_mgr.open("/etc/config", FileMode::ReadWrite).unwrap();
        
        println!("应用：打开了文件 '{}'", file.path);
        
        // 读写文件
        let mut read_buffer = [0u8; 100];
        let read_size = file_mgr.read(&file, &mut read_buffer).unwrap();
        
        println!("应用：读取了 {} 字节数据", read_size);
        
        let write_buffer = [42u8; 50];
        let write_size = file_mgr.write(&file, &write_buffer).unwrap();
        
        println!("应用：写入了 {} 字节数据", write_size);
        
        // 关闭文件（显式释放）
        file_mgr.close(file);
    }
    
    // 进程管理示例
    {
        let mut process_mgr = ProcessManager::new(&mut kernel);
        
        // 创建进程
        let new_process = process_mgr.create_process();
        
        println!("应用：创建了进程 PID {}", new_process.pid);
        
        // 启动进程
        let running_process = process_mgr.start_process(new_process).unwrap();
        
        println!("应用：启动了进程 PID {}", running_process.pid);
        
        // 挂起进程
        let suspended_process = process_mgr.suspend_process(running_process).unwrap();
        
        println!("应用：挂起了进程 PID {}", suspended_process.pid);
        
        // 终止进程
        let terminated_process = process_mgr.terminate_process(suspended_process);
        
        println!("应用：终止了进程 PID {}", terminated_process.pid);
        
        // 回收进程资源
        process_mgr.reap_process(terminated_process);
    }
    
    // 检查资源泄漏
    if kernel.active_resources.is_empty() {
        println!("内核：所有资源已正确释放");
    } else {
        println!("警告：检测到 {} 个资源泄漏", kernel.active_resources.len());
    }
}
```

### 驱动开发安全模型

Rust 所有权系统如何提高设备驱动安全性：

1. **设备访问安全**
   - 所有权型驱动接口设计
   - 类型安全的设备寄存器访问

2. **并发设备控制**
   - 无锁设备访问模式
   - 借用规则确保设备独占

3. **中断处理安全**
   - 中断上下文的资源安全
   - 安全的异步设备交互

```rust
// 驱动开发安全模型示例

// 1. 设备寄存器抽象
#[derive(Clone, Copy)]
struct RegisterAddress(usize);

// 寄存器包装器
struct Register<T> {
    address: RegisterAddress,
    _marker: std::marker::PhantomData<T>,
}

impl<T> Register<T> {
    fn new(address: RegisterAddress) -> Self {
        Register {
            address,
            _marker: std::marker::PhantomData,
        }
    }
}

// 寄存器访问特性
trait ReadableRegister<T> {
    fn read(&self) -> T;
}

trait WritableRegister<T> {
    fn write(&mut self, value: T);
}

// 针对 u32 的实现
impl ReadableRegister<u32> for Register<u32> {
    fn read(&self) -> u32 {
        // 在实际系统中，这里会进行真正的内存映射读取
        println!("读取寄存器 {:?}", self.address.0);
        0xDEADBEEF // 模拟的寄存器值
    }
}

impl WritableRegister<u32> for Register<u32> {
    fn write(&mut self, value: u32) {
        // 在实际系统中，这里会进行真正的内存映射写入
        println!("写入寄存器 {:?}，值: 0x{:X}", self.address.0, value);
    }
}

// 2. 设备抽象
struct Device {
    name: &'static str,
    control_reg: Register<u32>,
    status_reg: Register<u32>,
    data_reg: Register<u32>,
}

impl Device {
    fn new(name: &'static str, base_addr: usize) -> Self {
        Device {
            name,
            control_reg: Register::new(RegisterAddress(base_addr + 0x00)),
            status_reg: Register::new(RegisterAddress(base_addr + 0x04)),
            data_reg: Register::new(RegisterAddress(base_addr + 0x08)),
        }
    }
    
    // 初始化设备
    fn initialize(&mut self) {
        println!("初始化设备 '{}'", self.name);
        
        // 复位设备
        self.control_reg.write(0x1);
        
        // 等待设备就绪
        while (self.status_reg.read() & 0x1) == 0 {
            println!("等待设备就绪...");
        }
        
        println!("设备 '{}' 就绪", self.name);
    }
    
    // 发送数据
    fn send_data(&mut self, data: u32) -> Result<(), &'static str> {
        // 检查设备状态
        let status = self.status_reg.read();
        
        if (status & 0x2) == 0 {
            return Err("设备未准备好发送数据");
        }
        
        // 写入数据
        self.data_reg.write(data);
        
        // 触发发送
        self.control_reg.write(0x2);
        
        println!("发送数据 0x{:X} 到设备 '{}'", data, self.name);
        
        Ok(())
    }
    
    // 接收数据
    fn receive_data(&mut self) -> Result<u32, &'static str> {
        // 检查设备状态
        let status = self.status_reg.read();
        
        if (status & 0x4) == 0 {
            return Err("没有可接收的数据");
        }
        
        // 读取数据
        let data = self.data_reg.read();
        
        // 清除接收标志
        self.control_reg.write(0x4);
        
        println!("从设备 '{}' 接收数据 0x{:X}", self.name, data);
        
        Ok(data)
    }
    
    // 关闭设备
    fn shutdown(&mut self) {
        println!("关闭设备 '{}'", self.name);
        
        // 发送关闭指令
        self.control_reg.write(0x8);
    }
}

// 3. 中断安全的设备驱动
struct InterruptContext {
    device: *mut Device,
    enabled: bool,
}

// 中断处理状态
enum InterruptState {
    Disabled,
    Enabled,
}

// 中断控制器 
struct InterruptController {
    state: InterruptState,
    handlers: std::collections::HashMap<u32, InterruptContext>,
}

impl InterruptController {
    fn new() -> Self {
        InterruptController {
            state: InterruptState::Disabled,
            handlers: std::collections::HashMap::new(),
        }
    }
    
    // 注册中断处理程序
    fn register_handler(&mut self, irq: u32, device: &mut Device) {
        println!("注册设备 '{}' 的中断处理程序，IRQ {}", device.name, irq);
        
        self.handlers.insert(irq, InterruptContext {
            device: device as *mut Device,
            enabled: false,
        });
    }
    
    // 启用中断
    fn enable(&mut self) {
        println!("全局启用中断");
        self.state = InterruptState::Enabled;
    }
    
    // 禁用中断
    fn disable(&mut self) {
        println!("全局禁用中断");
        self.state = InterruptState::Disabled;
    }
    
    // 启用特定中断
    fn enable_irq(&mut self, irq: u32) -> Result<(), &'static str> {
        if let Some(context) = self.handlers.get_mut(&irq) {
            println!("启用 IRQ {}", irq);
            context.enabled = true;
            Ok(())
        } else {
            Err("未找到 IRQ 处理程序")
        }
    }
    
    // 禁用特定中断
    fn disable_irq(&mut self, irq: u32) -> Result<(), &'static str> {
        if let Some(context) = self.handlers.get_mut(&irq) {
            println!("禁用 IRQ {}", irq);
            context.enabled = false;
            Ok(())
        } else {
            Err("未找到 IRQ 处理程序")
        }
    }
    
    // 模拟触发中断
    fn simulate_interrupt(&mut self, irq: u32) {
        println!("模拟触发 IRQ {}", irq);
        
        match self.state {
            InterruptState::Disabled => {
                println!("中断被全局禁用，忽略");
                return;
            }
            InterruptState::Enabled => {}
        }
        
        if let Some(context) = self.handlers.get(&irq) {
            if !context.enabled {
                println!("IRQ {} 被禁用，忽略", irq);
                return;
            }
            
            println!("处理 IRQ {}", irq);
            
            // 安全地访问设备
            // 注意：这是为了演示。在实际系统中，我们需要更多的安全考虑
            let device = unsafe { &mut *context.device };
            
            // 读取设备状态
            let status = device.status_reg.read();
            println!("中断处理程序：设备 '{}' 状态 0x{:X}", device.name, status);
            
            // 处理中断
            if (status & 0x4) != 0 {
                // 数据可用中断
                match device.receive_data() {
                    Ok(data) => println!("中断处理程序：接收到数据 0x{:X}", data),
                    Err(e) => println!("中断处理程序：接收数据错误: {}", e),
                }
            }
            
            // 清除中断
            device.control_reg.write(0x10);
        } else {
            println!("未找到 IRQ {} 的处理程序", irq);
        }
    }
}

// 4. 设备驱动管理器
struct DriverManager {
    devices: Vec<Device>,
    interrupt_controller: InterruptController,
}

impl DriverManager {
    fn new() -> Self {
        DriverManager {
            devices: Vec::new(),
            interrupt_controller: InterruptController::new(),
        }
    }
    
    // 注册设备
    fn register_device(&mut self, device: Device) {
        println!("注册设备 '{}'", device.name);
        self.devices.push(device);
    }
    
    // 获取设备引用
    fn get_device(&mut self, name: &str) -> Option<&mut Device> {
        self.devices.iter_mut().find(|dev| dev.name == name)
    }
    
    // 初始化所有设备
    fn initialize_all(&mut self) {
        println!("初始化所有设备");
        
        for device in &mut self.devices {
            device.initialize();
        }
        
        // 设置中断
        for (i, device) in self.devices.iter_mut().enumerate() {
            self.interrupt_controller.register_handler(i as u32, device);
            self.interrupt_controller.enable_irq(i as u32).unwrap();
        }
        
        // 启用中断
        self.interrupt_controller.enable();
    }
    
    // 关闭所有设备
    fn shutdown_all(&mut self) {
        println!("关闭所有设备");
        
        // 禁用中断
        self.interrupt_controller.disable();
        
        for device in &mut self.devices {
            device.shutdown();
        }
    }
    
    // 模拟设备中断
    fn simulate_interrupt(&mut self, irq: u32) {
        self.interrupt_controller.simulate_interrupt(irq);
    }
}

// 驱动开发示例
fn driver_development_example() {
    // 创建驱动管理器
    let mut driver_mgr = DriverManager::new();
    
    // 注册设备
    driver_mgr.register_device(Device::new("UART0", 0x10000000));
    driver_mgr.register_device(Device::new("SPI1", 0x20000000));
    
    // 初始化所有设备
    driver_mgr.initialize_all();
    
    // 获取 UART 设备并发送数据
    if let Some(uart) = driver_mgr.get_device("UART0") {
        uart.send_data(0x12345678).unwrap();
    }
    
    // 模拟中断
    driver_mgr.simulate_interrupt(0); // UART0 中断
    
    // 模拟 SPI 设备操作
    if let Some(spi) = driver_mgr.get_device("SPI1") {
        spi.send_data(0xAABBCCDD).unwrap();
    }
    
    // 模拟另一个中断
    driver_mgr.simulate_interrupt(1); // SPI1 中断
    
    // 关闭所有设备
    driver_mgr.shutdown_all();
}
```

### 权限系统与所有权映射

操作系统权限系统如何与所有权模型映射：

1. **权限即能力**
   - 将权限视为资源能力
   - 操作系统权限的所有权表示

2. **安全能力转移**
   - 所有权系统保障能力安全转移
   - 防止权限提升漏洞

3. **权限分离与借用**
   - 借用系统实现权限最小化
   - 细粒度的临时权限授予

```rust
// 权限系统与所有权映射示例

// 1. 基础权限模型
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Permission {
    Read,
    Write,
    Execute,
}

// 权限集
#[derive(Clone, Debug)]
struct PermissionSet {
    perms: Vec<Permission>,
}

impl PermissionSet {
    fn new() -> Self {
        PermissionSet {
            perms: Vec::new(),
        }
    }
    
    fn add(&mut self, perm: Permission) {
        if !self.perms.contains(&perm) {
            self.perms.push(perm);
        }
    }
    
    fn has(&self, perm: Permission) -> bool {
        self.perms.contains(&perm)
    }
    
    // 创建权限子集
    fn subset(&self, requested: &[Permission]) -> PermissionSet {
        let mut subset = PermissionSet::new();
        
        for perm in requested {
            if self.has(*perm) {
                subset.add(*perm);
            }
        }
        
        subset
    }
}

// 2. 用户和资源模型
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
struct UserId(u32);

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
struct ResourceId(u32);

// 受保护资源
struct ProtectedResource {
    id: ResourceId,
    name: String,
    content: Vec<u8>,
}

// 3. 权限管理器
struct PermissionManager {
    user_permissions: std::collections::HashMap<UserId, std::collections::HashMap<ResourceId, PermissionSet>>,
    resources: std::collections::HashMap<ResourceId, ProtectedResource>,
    next_resource_id: u32,
}

impl PermissionManager {
    fn new() -> Self {
        PermissionManager {
            user_permissions: std::collections::HashMap::new(),
            resources: std::collections::HashMap::new(),
            next_resource_id: 1,
        }
    }
    
    // 添加资源
    fn add_resource(&mut self, name: &str, content: Vec<u8>) -> ResourceId {
        let id = ResourceId(self.next_resource_id);
        self.next_resource_id += 1;
        
        let resource = ProtectedResource {
            id,
            name: name.to_string(),
            content,
        };
        
        self.resources.insert(id, resource);
        
        println!("添加资源 '{}', ID: {:?}", name, id);
        
        id
    }
    
    // 授予用户对资源的权限
    fn grant_permission(&mut self, user: UserId, resource: ResourceId, perm: Permission) {
        let user_perms = self.user_permissions
            .entry(user)
            .or_insert_with(std::collections::HashMap::new);
            
        let resource_perms = user_perms
            .entry(resource)
            .or_insert_with(PermissionSet::new);
            
        resource_perms.add(perm);
        
        println!("授予用户 {:?} 对资源 {:?} 的 {:?} 权限", user, resource, perm);
    }
    
    // 检查用户是否具有特定权限
    fn check_permission(&self, user: UserId, resource: ResourceId, perm: Permission) -> bool {
        self.user_permissions
            .get(&user)
            .and_then(|perms| perms.get(&resource))
            .map_or(false, |perm_set| perm_set.has(perm))
    }
    
    // 创建访问令牌（实现所有权转移的权限）
    fn create_access_token(&self, user: UserId, resource: ResourceId, requested: &[Permission]) -> Option<AccessToken> {
        // 查找用户的资源权限
        let user_resource_perms = self.user_permissions
            .get(&user)
            .and_then(|perms| perms.get(&resource))?;
            
        // 创建请求权限的子集
        let granted_perms = user_resource_perms.subset(requested);
        
        // 如果没有授予任何权限，返回 None
        if granted_perms.perms.is_empty() {
            return None;
        }
        
        Some(AccessToken {
            user,
            resource,
            permissions: granted_perms,
        })
    }
    
    // 使用访问令牌读取资源
    fn read_resource(&self, token: &AccessToken) -> Result<&[u8], &'static str> {
        // 验证读取权限
        if !token.permissions.has(Permission::Read) {
            return Err("没有读取权限");
        }
        
        // 获取资源
        let resource = self.resources.get(&token.resource)
            .ok_or("资源不存在")?;
            
        println!("用户 {:?} 读取资源 '{}'", token.user, resource.name);
        
        Ok(&resource.content)
    }
    
    // 使用访问令牌写入资源
    fn write_resource(&mut self, token: &AccessToken, data: &[u8]) -> Result<(), &'static str> {
        // 验证写入权限
        if !token.permissions.has(Permission::Write) {
            return Err("没有写入权限");
        }
        
        // 获取资源
        let resource = self.resources.get_mut(&token.resource)
            .ok_or("资源不存在")?;
            
        // 更新资源内容
        resource.content = data.to_vec();
        
        println!("用户 {:?} 写入资源 '{}'", token.user, resource.name);
        
        Ok(())
    }
}

// 访问令牌（能力模型）
#[derive(Clone, Debug)]
struct AccessToken {
    user: UserId,
    resource: ResourceId,
    permissions: PermissionSet,
}

// 4. 权限代理（权限借用）
struct PermissionProxy<'a> {
    manager: &'a mut PermissionManager,
    token: AccessToken,
}

impl<'a> PermissionProxy<'a> {
    fn new(manager: &'a mut PermissionManager, token: AccessToken) -> Self {
        PermissionProxy {
            manager,
            token,
        }
    }
    
    // 读取资源（通过借用使用权限）
    fn read(&self) -> Result<&[u8], &'static str> {
        self.manager.read_resource(&self.token)
    }
    
    // 写入资源（通过可变借用使用权限）
    fn write(&mut self, data: &[u8]) -> Result<(), &'static str> {
        self.manager.write_resource(&self.token, data)
    }
    
    // 创建有限权限的子代理（进一步的权限借用）
    fn create_subproxy(&self, permissions: &[Permission]) -> Result<SubProxy, &'static str> {
        // 验证当前代理具有请求的所有权限
        for perm in permissions {
            if !self.token.permissions.has(*perm) {
                return Err("没有足够的权限创建子代理");
            }
        }
        
        // 创建子令牌
        let sub_token = AccessToken {
            user: self.token.user,
            resource: self.token.resource,
            permissions: self.token.permissions.subset(permissions),
        };
        
        Ok(SubProxy { token: sub_token })
    }
}

// 权限子代理（进一步的权限借用）
struct SubProxy {
    token: AccessToken,
}

impl SubProxy {
    // 获取当前权限
    fn get_permissions(&self) -> &PermissionSet {
        &self.token.permissions
    }
}

// 权限系统示例
fn permission_system_example() {
    // 创建权限管理器
    let mut perm_mgr = PermissionManager::new();
    
    // 创建用户
    let alice = UserId(1);
    let bob = UserId(2);
    
    // 创建资源
    let document = perm_mgr.add_resource("secret_document.txt", b"This is a secret document".to_vec());
    let database = perm_mgr.add_resource("user_database.db", b"user data...".to_vec());
    
    // 授予权限
    perm_mgr.grant_permission(alice, document, Permission::Read);
    perm_mgr.grant_permission(alice, document, Permission::Write);
    perm_mgr.grant_permission(alice, database, Permission::Read);
    
    perm_mgr.grant_permission(bob, database, Permission::Read);
    perm_mgr.grant_permission(bob, database, Permission::Write);
    
    // 创建访问令牌（将权限视为所有权资源）
    let alice_doc_token = perm_mgr.create_access_token(
        alice, 
        document, 
        &[Permission::Read, Permission::Write]
    ).unwrap();
    
    // 使用访问令牌
    if let Ok(content) = perm_mgr.read_resource(&alice_doc_token) {
        println!("文档内容: {}", String::from_utf8_lossy(content));
    }
    
    // 创建权限代理（通过借用使用权限）
    let mut alice_proxy = PermissionProxy::new(&mut perm_mgr, alice_doc_token);
    
    // 通过代理读取
    if let Ok(content) = alice_proxy.read() {
        println!("通过代理读取: {}", String::from_utf8_lossy(content));
    }
    
    // 通过代理写入
    let new_content = b"Updated document content".to_vec();
    alice_proxy.write(&new_content).unwrap();
    
    // 创建有限权限的子代理
    let read_only_proxy = alice_proxy.create_subproxy(&[Permission::Read]).unwrap();
    
    // 检查子代理权限
    let sub_perms = read_only_proxy.get_permissions();
    println!("子代理权限: {:?}", sub_perms);
    
    // 尝试创建没有权限的令牌
    let bob_doc_token = perm_mgr.create_access_token(
        bob, 
        document, 
        &[Permission::Read]
    );
    
    match bob_doc_token {
        Some(_) => println!("Bob 可以访问文档 (不应该发生)"),
        None => println!("Bob 无法获得文档访问权限"),
    }
}
```

### 操作系统抽象层的所有权

操作系统抽象层如何使用所有权：

1. **安全系统调用接口**
   - 所有权表达系统调用语义
   - 防止资源使用错误

2. **进程通信与所有权转移**
   - 进程间通信的所有权模型
   - 共享内存的安全访问

3. **OS 级零拷贝实现**
   - 使用所有权实现零拷贝操作
   - 提高系统调用性能

```rust
// 操作系统抽象层的所有权示例

// 1. 系统调用接口
struct Syscall;

// 文件描述符
#[derive(Debug, Clone, Copy)]
struct FileDescriptor(i32);

// 操作系统错误
#[derive(Debug)]
enum OsError {
    FileNotFound,
    PermissionDenied,
    InvalidDescriptor,
    IoError,
}

// 系统调用结果
type SysResult<T> = Result<T, OsError>;

impl Syscall {
    // 打开文件系统调用
    fn open(path: &str, flags: u32) -> SysResult<FileDescriptor> {
        println!("系统调用: 打开文件 '{}', 标志 0x{:X}", path, flags);
        
        // 模拟系统调用实现
        if path.contains("nonexistent") {
            return Err(OsError::FileNotFound);
        }
        
        if flags & 0x2 != 0 && path.contains("readonly") {
            return Err(OsError::PermissionDenied);
        }
        
        // 分配文件描述符
        static mut NEXT_FD: i32 = 3; // 0, 1, 2 是标准输入、输出、错误
        let fd = unsafe {
            let fd = NEXT_FD;
            NEXT_FD += 1;
            fd
        };
        
        Ok(FileDescriptor(fd))
    }
    
    // 读取文件系统调用
    fn read(fd: FileDescriptor, buffer: &mut [u8]) -> SysResult<usize> {
        println!("系统调用: 从 {:?} 读取最多 {} 字节", fd, buffer.len());
        
        if fd.0 < 0 {
            return Err(OsError::InvalidDescriptor);
        }
        
        // 模拟读取数据
        let data = b"Hello from the kernel!";
        let read_size = std::cmp::min(buffer.len(), data.len());
        
        buffer[..read_size].copy_from_slice(&data[..read_size]);
        
        Ok(read_size)
    }
    
    // 写入文件系统调用
    fn write(fd: FileDescriptor, buffer: &[u8]) -> SysResult<usize> {
        println!("系统调用: 向 {:?} 写入 {} 字节", fd, buffer.len());
        
        if fd.0 < 0 {
            return Err(OsError::InvalidDescriptor);
        }
        
        // 模拟写入
        println!("写入数据: {}", String::from_utf8_lossy(buffer));
        
        Ok(buffer.len())
    }
    
    // 关闭文件系统调用 - 消耗文件描述符（所有权语义）
    fn close(fd: FileDescriptor) -> SysResult<()> {
        println!("系统调用: 关闭文件 {:?}", fd);
        
        if fd.0 < 0 {
            return Err(OsError::InvalidDescriptor);
        }
        
        // 文件描述符被消耗，不能再使用
        Ok(())
    }
}

// 2. 进程和内存抽象
#[derive(Debug, Clone, Copy)]
struct ProcessId(u32);

#[derive(Debug)]
struct Process {
    id: ProcessId,
    name: String,
    fds: Vec<FileDescriptor>,
}

// 内存映射区域
struct MemoryMapping {
    address: usize,
    size: usize,
    protection: u32, // 保护标志：读、写、执行
}

// 共享内存区域
struct SharedMemory {
    id: u32,
    size: usize,
    address: usize,
}

// 内存管理
struct MemoryManager;

impl MemoryManager {
    // 分配内存
    fn allocate(&self, size: usize) -> *mut u8 {
        println!("内存管理器: 分配 {} 字节", size);
        // 模拟内存分配
        std::ptr::null_mut()
    }
    
    // 释放内存 - 消耗指针（所有权语义）
    fn free(&self, ptr: *mut u8, size: usize) {
        println!("内存管理器: 释放 {} 字节于 {:?}", size, ptr);
        // 模拟内存释放
    }
    
    // 创建共享内存
    fn create_shared_memory(&self, size: usize) -> SysResult<SharedMemory> {
        println!("内存管理器: 创建 {} 字节共享内存", size);
        
        // 分配共享内存 ID
        static mut NEXT_ID: u32 = 1;
        let id = unsafe {
            let id = NEXT_ID;
            NEXT_ID += 1;
            id
        };
        
        Ok(SharedMemory {
            id,
            size,
            address: 0x8000_0000, // 模拟地址
        })
    }
    
    // 映射共享内存到进程
    fn map_shared_memory(&self, shared_mem: &SharedMemory, process: &mut Process) -> SysResult<MemoryMapping> {
        println!("内存管理器: 映射共享内存 {} 到进程 {:?}", shared_mem.id, process.id);
        
        Ok(MemoryMapping {
            address: shared_mem.address,
            size: shared_mem.size,
            protection: 0x7, // 读、写、执行
        })
    }
    
    // 解除内存映射 - 消耗映射（所有权语义）
    fn unmap(&self, mapping: MemoryMapping) {
        println!("内存管理器: 解除地址 0x{:X} 处 {} 字节的映射", mapping.address, mapping.size);
        // 模拟解除映射
    }
}

// 3. 进程间通信
struct MessageQueue {
    id: u32,
}

// 消息
struct Message {
    type_id: u32,
    data: Vec<u8>,
}

// 消息队列管理
struct IpcManager;

impl IpcManager {
    // 创建消息队列
    fn create_queue(&self) -> SysResult<MessageQueue> {
        // 分配 ID
        static mut NEXT_ID: u32 = 1;
        let id = unsafe {
            let id = NEXT_ID;
            NEXT_ID += 1;
            id
        };
        
        println!("IPC 管理器: 创建消息队列 {}", id);
        
        Ok(MessageQueue { id })
    }
    
    // 发送消息 - 消耗消息（所有权语义）
    fn send(&self, queue: &MessageQueue, message: Message) -> SysResult<()> {
        println!("IPC 管理器: 发送类型 {} 的消息到队列 {}", message.type_id, queue.id);
        
        // 消息被消耗，发送者不能再访问
        println!("发送 {} 字节数据", message.data.len());
        
        Ok(())
    }
    
    // 接收消息 - 创建消息（所有权语义）
    fn receive(&self, queue: &MessageQueue) -> SysResult<Message> {
        println!("IPC 管理器: 从队列 {} 接收消息", queue.id);
        
        // 模拟接收消息
        Ok(Message {
            type_id: 1,
            data: b"IPC message".to_vec(),
        })
    }
    
    // 删除消息队列 - 消耗队列（所有权语义）
    fn delete_queue(&self, queue: MessageQueue) -> SysResult<()> {
        println!("IPC 管理器: 删除消息队列 {}", queue.id);
        // 队列被消耗，不能再使用
        Ok(())
    }
}

// 4. 零拷贝操作
struct DmaBuffer {
    address: usize,
    size: usize,
}

// 实现零拷贝 I/O
struct ZeroCopyIo;

impl ZeroCopyIo {
    // 分配 DMA 缓冲区
    fn allocate_dma_buffer(&self, size: usize) -> SysResult<DmaBuffer> {
        println!("零拷贝 I/O: 分配 {} 字节 DMA 缓冲区", size);
        
        // 模拟 DMA 缓冲区分配
        Ok(DmaBuffer {
            address: 0x9000_0000, // 模拟地址
            size,
        })
    }
    
    // 从文件读取到 DMA 缓冲区（零拷贝）
    fn read_into_dma(&self, fd: FileDescriptor, buffer: &mut DmaBuffer) -> SysResult<usize> {
        println!("零拷贝 I/O: 从 {:?} 直接读取到 DMA 缓冲区 (地址 0x{:X})", fd, buffer.address);
        
        // 模拟零拷贝读取
        // 在实际系统中，这会直接将数据从设备 DMA 到缓冲区，跳过中间复制
        let read_size = buffer.size.min(1024); // 假设读取最多 1024 字节
        
        Ok(read_size)
    }
    
    // 从 DMA 缓冲区写入到文件（零拷贝）
    fn write_from_dma(&self, fd: FileDescriptor, buffer: &DmaBuffer) -> SysResult<usize> {
        println!("零拷贝 I/O: 从 DMA 缓冲区 (地址 0x{:X}) 直接写入到 {:?}", buffer.address, fd);
        
        // 模拟零拷贝写入
        Ok(buffer.size)
    }
    
    // 释放 DMA 缓冲区 - 消耗缓冲区（所有权语义）
    fn free_dma_buffer(&self, buffer: DmaBuffer) {
        println!("零拷贝 I/O: 释放 DMA 缓冲区 (地址 0x{:X})", buffer.address);
        // 缓冲区被消耗，不能再使用
    }
}

// 操作系统抽象层示例
fn os_abstraction_example() {
    // 1. 系统调用接口示例
    println!("\n=== 系统调用接口示例 ===");
    
    // 打开文件
    let fd = match Syscall::open("/home/user/document.txt", 0x1) {
        Ok(fd) => {
            println!("成功打开文件: {:?}", fd);
            fd
        },
        Err(e) => {
            println!("打开文件失败: {:?}", e);
            return;
        }
    };
    
    // 读取文件
    let mut buffer = [0u8; 128];
    match Syscall::read(fd, &mut buffer) {
        Ok(size) => {
            println!("读取了 {} 字节: {}", size, String::from_utf8_lossy(&buffer[..size]));
        },
        Err(e) => {
            println!("读取失败: {:?}", e);
        }
    }
    
    // 写入文件
    let data = b"Hello, operating system!";
    match Syscall::write(fd, data) {
        Ok(size) => {
            println!("写入了 {} 字节", size);
        },
        Err(e) => {
            println!("写入失败: {:?}", e);
        }
    }
    
    // 关闭文件 - 消耗文件描述符
    match Syscall::close(fd) {
        Ok(_) => {
            println!("成功关闭文件");
        },
        Err(e) => {
            println!("关闭文件失败: {:?}", e);
        }
    }
    
    // 尝试再次使用已关闭的文件描述符
    // 在实际代码中，这会导致编译错误，因为 fd 已被消耗
    // 这里仅作为概念演示
    println!("尝试再次使用已关闭的文件描述符 (在真实代码中会导致编译错误)");
    
    // 2. 内存管理示例
    println!("\n=== 内存管理示例 ===");
    
    let memory_mgr = MemoryManager;
    
    // 分配内存
    let ptr = memory_mgr.allocate(1024);
    println!("分配的内存指针: {:?}", ptr);
    
    // 释放内存 - 消耗指针
    memory_mgr.free(ptr, 1024);
    
    // 创建共享内存
    let shared_mem = memory_mgr.create_shared_memory(4096).unwrap();
    println!("创建的共享内存: id={}, 大小={}", shared_mem.id, shared_mem.size);
    
    // 创建两个进程
    let mut process1 = Process {
        id: ProcessId(1),
        name: "Process1".to_string(),
        fds: Vec::new(),
    };
    
    let mut process2 = Process {
        id: ProcessId(2),
        name: "Process2".to_string(),
        fds: Vec::new(),
    };
    
    // 映射共享内存到两个进程
    let mapping1 = memory_mgr.map_shared_memory(&shared_mem, &mut process1).unwrap();
    let mapping2 = memory_mgr.map_shared_memory(&shared_mem, &mut process2).unwrap();
    
    println!("进程 1 映射: 地址=0x{:X}, 大小={}", mapping1.address, mapping1.size);
    println!("进程 2 映射: 地址=0x{:X}, 大小={}", mapping2.address, mapping2.size);
    
    // 解除映射 - 消耗映射对象
    memory_mgr.unmap(mapping1);
    memory_mgr.unmap(mapping2);
    
    // 3. IPC 示例
    println!("\n=== IPC 示例 ===");
    
    let ipc_mgr = IpcManager;
    
    // 创建消息队列
    let queue = ipc_mgr.create_queue().unwrap();
    
    // 创建消息
    let message = Message {
        type_id: 42,
        data: b"Important IPC message".to_vec(),
    };
    
    // 发送消息 - 消耗消息
    ipc_mgr.send(&queue, message).unwrap();
    
    // 消息已被消耗，无法再次使用
    println!("消息已被消耗，在真实代码中无法再次访问");
    
    // 接收消息 - 创建新消息
    let received = ipc_mgr.receive(&queue).unwrap();
    println!("接收到消息: 类型={}, 数据='{}'", 
        received.type_id, String::from_utf8_lossy(&received.data));
    
    // 删除队列 - 消耗队列
    ipc_mgr.delete_queue(queue).unwrap();
    
    // 4. 零拷贝 I/O 示例
    println!("\n=== 零拷贝 I/O 示例 ===");
    
    let zc_io = ZeroCopyIo;
    
    // 分配 DMA 缓冲区
    let mut dma_buffer = zc_io.allocate_dma_buffer(8192).unwrap();
    println!("分配的 DMA 缓冲区: 地址=0x{:X}, 大小={}", dma_buffer.address, dma_buffer.size);
    
    // 打开文件
    let fd2 = Syscall::open("/dev/sda", 0x2).unwrap();
    
    // 零拷贝读取
    let read_size = zc_io.read_into_dma(fd2, &mut dma_buffer).unwrap();
    println!("零拷贝读取了 {} 字节到 DMA 缓冲区", read_size);
    
    // 零拷贝写入
    let written_size = zc_io.write_from_dma(fd2, &dma_buffer).unwrap();
    println!("零拷贝写入了 {} 字节到文件", written_size);
    
    // 关闭文件 - 消耗文件描述符
    Syscall::close(fd2).unwrap();
    
    // 释放 DMA 缓冲区 - 消耗缓冲区
    zc_io.free_dma_buffer(dma_buffer);
    
    println!("\n操作系统抽象层示例完成");
}
```
