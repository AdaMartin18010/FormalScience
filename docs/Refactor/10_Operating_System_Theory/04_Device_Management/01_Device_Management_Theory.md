# 10.4.1 设备管理理论

## 📋 概述

设备管理理论研究操作系统中I/O设备的控制、调度和优化机制。该理论涵盖设备驱动、I/O调度、中断处理、设备抽象等核心概念，为硬件与软件交互提供理论基础。

## 1. 基本概念

### 1.1 设备管理定义

**定义 1.1**（设备管理）
设备管理是操作系统对I/O设备进行控制、调度和优化的机制。

### 1.2 设备类型分类

| 设备类型     | 英文名称         | 描述                         | 典型代表         |
|--------------|------------------|------------------------------|------------------|
| 字符设备     | Character Device | 按字符传输数据的设备         | 键盘、鼠标       |
| 块设备       | Block Device     | 按数据块传输的设备           | 硬盘、SSD        |
| 网络设备     | Network Device   | 网络通信设备                 | 网卡、调制解调器 |
| 特殊设备     | Special Device   | 系统特殊功能设备             | 时钟、中断控制器 |

## 2. 形式化定义

### 2.1 设备抽象

**定义 2.1**（设备抽象）
设备抽象是将物理设备映射为逻辑接口的过程，隐藏硬件细节。

### 2.2 I/O调度

**定义 2.2**（I/O调度）
I/O调度是决定多个I/O请求执行顺序的算法。

### 2.3 中断处理

**定义 2.3**（中断处理）
中断处理是响应硬件中断信号的机制，实现异步I/O。

## 3. 定理与证明

### 3.1 I/O调度效率定理

**定理 3.1**（电梯算法最优性）
电梯算法（SCAN）在磁头移动距离方面接近最优。

**证明**：
电梯算法按磁头移动方向处理请求，避免了磁头的来回移动，因此效率较高。□

### 3.2 中断延迟定理

**定理 3.2**（中断延迟）
中断延迟是中断发生到处理开始的时间间隔。

**证明**：
中断延迟包括硬件延迟、软件延迟和调度延迟的总和。□

## 4. Rust代码实现

### 4.1 设备抽象层实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

#[derive(Debug, Clone)]
pub enum DeviceType {
    Character,
    Block,
    Network,
    Special,
}

#[derive(Debug, Clone)]
pub struct DeviceInfo {
    pub device_id: u32,
    pub device_type: DeviceType,
    pub name: String,
    pub major_number: u32,
    pub minor_number: u32,
    pub is_available: bool,
}

pub trait DeviceDriver {
    fn open(&mut self) -> Result<(), String>;
    fn close(&mut self) -> Result<(), String>;
    fn read(&mut self, buffer: &mut [u8]) -> Result<usize, String>;
    fn write(&mut self, buffer: &[u8]) -> Result<usize, String>;
    fn ioctl(&mut self, command: u32, arg: u64) -> Result<i32, String>;
}

#[derive(Debug, Clone)]
pub struct CharacterDevice {
    pub info: DeviceInfo,
    pub buffer: Vec<u8>,
    pub position: usize,
}

impl CharacterDevice {
    pub fn new(device_id: u32, name: String, major: u32, minor: u32) -> Self {
        CharacterDevice {
            info: DeviceInfo {
                device_id,
                device_type: DeviceType::Character,
                name,
                major_number: major,
                minor_number: minor,
                is_available: true,
            },
            buffer: Vec::new(),
            position: 0,
        }
    }
}

impl DeviceDriver for CharacterDevice {
    fn open(&mut self) -> Result<(), String> {
        if self.info.is_available {
            Ok(())
        } else {
            Err("Device is not available".to_string())
        }
    }
    
    fn close(&mut self) -> Result<(), String> {
        self.position = 0;
        Ok(())
    }
    
    fn read(&mut self, buffer: &mut [u8]) -> Result<usize, String> {
        let bytes_to_read = std::cmp::min(buffer.len(), self.buffer.len() - self.position);
        if bytes_to_read > 0 {
            buffer[..bytes_to_read].copy_from_slice(&self.buffer[self.position..self.position + bytes_to_read]);
            self.position += bytes_to_read;
        }
        Ok(bytes_to_read)
    }
    
    fn write(&mut self, buffer: &[u8]) -> Result<usize, String> {
        self.buffer.extend_from_slice(buffer);
        Ok(buffer.len())
    }
    
    fn ioctl(&mut self, _command: u32, _arg: u64) -> Result<i32, String> {
        Ok(0) // 默认成功
    }
}

#[derive(Debug, Clone)]
pub struct BlockDevice {
    pub info: DeviceInfo,
    pub blocks: Vec<Vec<u8>>,
    pub block_size: usize,
    pub total_blocks: usize,
}

impl BlockDevice {
    pub fn new(device_id: u32, name: String, major: u32, minor: u32, block_size: usize, total_blocks: usize) -> Self {
        BlockDevice {
            info: DeviceInfo {
                device_id,
                device_type: DeviceType::Block,
                name,
                major_number: major,
                minor_number: minor,
                is_available: true,
            },
            blocks: vec![vec![0; block_size]; total_blocks],
            block_size,
            total_blocks,
        }
    }
}

impl DeviceDriver for BlockDevice {
    fn open(&mut self) -> Result<(), String> {
        if self.info.is_available {
            Ok(())
        } else {
            Err("Device is not available".to_string())
        }
    }
    
    fn close(&mut self) -> Result<(), String> {
        Ok(())
    }
    
    fn read(&mut self, buffer: &mut [u8]) -> Result<usize, String> {
        let block_number = 0; // 简化实现，总是读取第一个块
        if block_number < self.total_blocks {
            let bytes_to_read = std::cmp::min(buffer.len(), self.block_size);
            buffer[..bytes_to_read].copy_from_slice(&self.blocks[block_number][..bytes_to_read]);
            Ok(bytes_to_read)
        } else {
            Err("Invalid block number".to_string())
        }
    }
    
    fn write(&mut self, buffer: &[u8]) -> Result<usize, String> {
        let block_number = 0; // 简化实现，总是写入第一个块
        if block_number < self.total_blocks {
            let bytes_to_write = std::cmp::min(buffer.len(), self.block_size);
            self.blocks[block_number][..bytes_to_write].copy_from_slice(&buffer[..bytes_to_write]);
            Ok(bytes_to_write)
        } else {
            Err("Invalid block number".to_string())
        }
    }
    
    fn ioctl(&mut self, _command: u32, _arg: u64) -> Result<i32, String> {
        Ok(0)
    }
}
```

### 4.2 I/O调度器实现

```rust
use std::collections::VecDeque;

#[derive(Debug, Clone)]
pub struct IORequest {
    pub request_id: u32,
    pub device_id: u32,
    pub operation: IOOperation,
    pub block_number: usize,
    pub data: Vec<u8>,
    pub priority: u32,
    pub timestamp: u64,
}

#[derive(Debug, Clone)]
pub enum IOOperation {
    Read,
    Write,
    Seek,
}

#[derive(Debug, Clone)]
pub enum IOScheduler {
    FirstComeFirstServed,
    ShortestSeekTimeFirst,
    SCAN,
    C_SCAN,
    LOOK,
}

#[derive(Debug, Clone)]
pub struct IOSchedulerManager {
    pub scheduler_type: IOScheduler,
    pub request_queue: VecDeque<IORequest>,
    pub current_head_position: usize,
    pub direction: ScanDirection,
}

#[derive(Debug, Clone)]
pub enum ScanDirection {
    Up,
    Down,
}

impl IOSchedulerManager {
    pub fn new(scheduler_type: IOScheduler) -> Self {
        IOSchedulerManager {
            scheduler_type,
            request_queue: VecDeque::new(),
            current_head_position: 0,
            direction: ScanDirection::Up,
        }
    }
    
    pub fn add_request(&mut self, request: IORequest) {
        self.request_queue.push_back(request);
        self.schedule_requests();
    }
    
    pub fn schedule_requests(&mut self) {
        match self.scheduler_type {
            IOScheduler::FirstComeFirstServed => {
                // FCFS不需要重新排序
            },
            IOScheduler::ShortestSeekTimeFirst => {
                self.sstf_schedule();
            },
            IOScheduler::SCAN => {
                self.scan_schedule();
            },
            IOScheduler::C_SCAN => {
                self.cscan_schedule();
            },
            IOScheduler::LOOK => {
                self.look_schedule();
            },
        }
    }
    
    fn sstf_schedule(&mut self) {
        // 最短寻道时间优先调度
        let mut min_distance = usize::MAX;
        let mut min_index = 0;
        
        for (index, request) in self.request_queue.iter().enumerate() {
            let distance = if request.block_number > self.current_head_position {
                request.block_number - self.current_head_position
            } else {
                self.current_head_position - request.block_number
            };
            
            if distance < min_distance {
                min_distance = distance;
                min_index = index;
            }
        }
        
        if min_index > 0 {
            let request = self.request_queue.remove(min_index).unwrap();
            self.request_queue.push_front(request);
        }
    }
    
    fn scan_schedule(&mut self) {
        // SCAN算法（电梯算法）
        let mut requests_above = Vec::new();
        let mut requests_below = Vec::new();
        
        for request in self.request_queue.drain(..) {
            if request.block_number >= self.current_head_position {
                requests_above.push(request);
            } else {
                requests_below.push(request);
            }
        }
        
        // 按方向排序
        match self.direction {
            ScanDirection::Up => {
                requests_above.sort_by_key(|r| r.block_number);
                requests_below.sort_by_key(|r| r.block_number);
                requests_below.reverse();
                
                for request in requests_above {
                    self.request_queue.push_back(request);
                }
                for request in requests_below {
                    self.request_queue.push_back(request);
                }
            },
            ScanDirection::Down => {
                requests_above.sort_by_key(|r| r.block_number);
                requests_below.sort_by_key(|r| r.block_number);
                requests_below.reverse();
                
                for request in requests_below {
                    self.request_queue.push_back(request);
                }
                for request in requests_above {
                    self.request_queue.push_back(request);
                }
            },
        }
    }
    
    fn cscan_schedule(&mut self) {
        // C-SCAN算法（循环扫描）
        let mut requests_above = Vec::new();
        let mut requests_below = Vec::new();
        
        for request in self.request_queue.drain(..) {
            if request.block_number >= self.current_head_position {
                requests_above.push(request);
            } else {
                requests_below.push(request);
            }
        }
        
        // 总是向上扫描
        requests_above.sort_by_key(|r| r.block_number);
        requests_below.sort_by_key(|r| r.block_number);
        
        for request in requests_above {
            self.request_queue.push_back(request);
        }
        for request in requests_below {
            self.request_queue.push_back(request);
        }
    }
    
    fn look_schedule(&mut self) {
        // LOOK算法（改进的SCAN）
        self.scan_schedule(); // 简化实现，使用SCAN的逻辑
    }
    
    pub fn get_next_request(&mut self) -> Option<IORequest> {
        if let Some(request) = self.request_queue.pop_front() {
            self.current_head_position = request.block_number;
            Some(request)
        } else {
            None
        }
    }
    
    pub fn get_queue_length(&self) -> usize {
        self.request_queue.len()
    }
}
```

### 4.3 中断处理系统实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

#[derive(Debug, Clone)]
pub struct InterruptRequest {
    pub irq_number: u32,
    pub device_id: u32,
    pub priority: u32,
    pub timestamp: u64,
    pub data: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct InterruptHandler {
    pub irq_number: u32,
    pub device_id: u32,
    pub handler_function: String, // 简化为字符串标识
    pub is_enabled: bool,
}

#[derive(Debug, Clone)]
pub struct InterruptController {
    pub handlers: HashMap<u32, InterruptHandler>,
    pub pending_interrupts: VecDeque<InterruptRequest>,
    pub interrupt_mask: u64,
    pub current_priority: u32,
}

impl InterruptController {
    pub fn new() -> Self {
        InterruptController {
            handlers: HashMap::new(),
            pending_interrupts: VecDeque::new(),
            interrupt_mask: 0,
            current_priority: 0,
        }
    }
    
    pub fn register_handler(&mut self, irq_number: u32, device_id: u32, handler_function: String) {
        let handler = InterruptHandler {
            irq_number,
            device_id,
            handler_function,
            is_enabled: true,
        };
        self.handlers.insert(irq_number, handler);
    }
    
    pub fn enable_interrupt(&mut self, irq_number: u32) {
        if let Some(handler) = self.handlers.get_mut(&irq_number) {
            handler.is_enabled = true;
            self.interrupt_mask |= 1 << irq_number;
        }
    }
    
    pub fn disable_interrupt(&mut self, irq_number: u32) {
        if let Some(handler) = self.handlers.get_mut(&irq_number) {
            handler.is_enabled = false;
            self.interrupt_mask &= !(1 << irq_number);
        }
    }
    
    pub fn raise_interrupt(&mut self, irq_number: u32, device_id: u32, data: Vec<u8>) {
        if let Some(handler) = self.handlers.get(&irq_number) {
            if handler.is_enabled {
                let request = InterruptRequest {
                    irq_number,
                    device_id,
                    priority: handler.irq_number, // 简化优先级
                    timestamp: std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_micros() as u64,
                    data,
                };
                self.pending_interrupts.push_back(request);
            }
        }
    }
    
    pub fn handle_interrupts(&mut self) -> Vec<InterruptRequest> {
        let mut handled_interrupts = Vec::new();
        
        // 按优先级排序中断请求
        let mut sorted_interrupts: Vec<_> = self.pending_interrupts.drain(..).collect();
        sorted_interrupts.sort_by_key(|irq| irq.priority);
        
        for interrupt in sorted_interrupts {
            if let Some(handler) = self.handlers.get(&interrupt.irq_number) {
                if handler.is_enabled {
                    // 执行中断处理程序
                    self.execute_handler(handler, &interrupt);
                    handled_interrupts.push(interrupt);
                }
            }
        }
        
        handled_interrupts
    }
    
    fn execute_handler(&self, handler: &InterruptHandler, interrupt: &InterruptRequest) {
        // 简化的中断处理程序执行
        println!("Executing handler {} for IRQ {}", handler.handler_function, interrupt.irq_number);
    }
    
    pub fn get_pending_count(&self) -> usize {
        self.pending_interrupts.len()
    }
    
    pub fn clear_all_interrupts(&mut self) {
        self.pending_interrupts.clear();
    }
}

#[derive(Debug, Clone)]
pub struct DeviceManager {
    pub devices: HashMap<u32, Arc<Mutex<Box<dyn DeviceDriver>>>>,
    pub interrupt_controller: InterruptController,
    pub io_scheduler: IOSchedulerManager,
}

impl DeviceManager {
    pub fn new() -> Self {
        DeviceManager {
            devices: HashMap::new(),
            interrupt_controller: InterruptController::new(),
            io_scheduler: IOSchedulerManager::new(IOScheduler::SCAN),
        }
    }
    
    pub fn register_device(&mut self, device_id: u32, device: Box<dyn DeviceDriver>) {
        let device_arc = Arc::new(Mutex::new(device));
        self.devices.insert(device_id, device_arc);
    }
    
    pub fn open_device(&mut self, device_id: u32) -> Result<(), String> {
        if let Some(device) = self.devices.get(&device_id) {
            if let Ok(mut device_guard) = device.lock() {
                device_guard.open()
            } else {
                Err("Failed to lock device".to_string())
            }
        } else {
            Err("Device not found".to_string())
        }
    }
    
    pub fn read_device(&mut self, device_id: u32, buffer: &mut [u8]) -> Result<usize, String> {
        if let Some(device) = self.devices.get(&device_id) {
            if let Ok(mut device_guard) = device.lock() {
                device_guard.read(buffer)
            } else {
                Err("Failed to lock device".to_string())
            }
        } else {
            Err("Device not found".to_string())
        }
    }
    
    pub fn write_device(&mut self, device_id: u32, buffer: &[u8]) -> Result<usize, String> {
        if let Some(device) = self.devices.get(&device_id) {
            if let Ok(mut device_guard) = device.lock() {
                device_guard.write(buffer)
            } else {
                Err("Failed to lock device".to_string())
            }
        } else {
            Err("Device not found".to_string())
        }
    }
    
    pub fn close_device(&mut self, device_id: u32) -> Result<(), String> {
        if let Some(device) = self.devices.get(&device_id) {
            if let Ok(mut device_guard) = device.lock() {
                device_guard.close()
            } else {
                Err("Failed to lock device".to_string())
            }
        } else {
            Err("Device not found".to_string())
        }
    }
}
```

## 5. 相关理论与交叉引用

- [进程管理理论](../01_Process_Management/01_Process_Management_Theory.md)
- [内存管理理论](../02_Memory_Management/01_Memory_Management_Theory.md)
- [文件系统理论](../03_File_Systems/01_File_Systems_Theory.md)

## 6. 参考文献

1. Silberschatz, A., Galvin, P. B., & Gagne, G. (2018). Operating System Concepts. Wiley.
2. Tanenbaum, A. S., & Bos, H. (2014). Modern Operating Systems. Pearson.
3. Love, R. (2010). Linux Kernel Development. Addison-Wesley.

---

**最后更新**: 2024年12月21日  
**维护者**: AI助手  
**版本**: v1.0
