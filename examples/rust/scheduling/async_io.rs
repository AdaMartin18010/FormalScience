/// 异步IO调度实现
/// 
/// 演示 epoll 风格的异步IO多路复用、Reactor模式、以及异步任务调度

use std::collections::HashMap;
use std::io::{self, Read, Write};
use std::net::TcpListener;
use std::os::raw::{c_int as RawFd};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

/// IO事件类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IoEventType {
    /// 可读
    Readable,
    /// 可写
    Writable,
    /// 错误
    Error,
    /// 断开连接
    Hup,
}

/// IO事件
#[derive(Debug)]
pub struct IoEvent {
    /// 文件描述符
    pub fd: RawFd,
    /// 事件类型
    pub event_type: IoEventType,
}

/// 简化版 Reactor（反应器）模式
/// 
/// Reactor 模式是事件驱动的IO多路复用模式的核心
pub struct Reactor {
    /// 事件发送通道
    event_sender: Sender<IoEvent>,
    /// 事件接收通道
    event_receiver: Arc<Mutex<Receiver<IoEvent>>>,
    /// 注册的回调函数
    handlers: Arc<Mutex<HashMap<RawFd, Box<dyn Fn(IoEvent) + Send>>>>,
    /// 运行状态
    running: Arc<Mutex<bool>>,
}

impl Reactor {
    /// 创建新的 Reactor
    pub fn new() -> Self {
        let (tx, rx) = channel();
        
        Self {
            event_sender: tx,
            event_receiver: Arc::new(Mutex::new(rx)),
            handlers: Arc::new(Mutex::new(HashMap::new())),
            running: Arc::new(Mutex::new(false)),
        }
    }

    /// 注册事件处理器
    pub fn register<F>(&self, fd: RawFd, handler: F)
    where
        F: Fn(IoEvent) + Send + 'static,
    {
        self.handlers.lock().unwrap().insert(fd, Box::new(handler));
    }

    /// 注销事件处理器
    pub fn unregister(&self, fd: RawFd) {
        self.handlers.lock().unwrap().remove(&fd);
    }

    /// 发送事件
    pub fn send_event(&self, event: IoEvent) {
        let _ = self.event_sender.send(event);
    }

    /// 运行事件循环
    pub fn run(&self) {
        *self.running.lock().unwrap() = true;
        println!("Reactor 事件循环启动");

        while *self.running.lock().unwrap() {
            if let Ok(event) = self.event_receiver.lock().unwrap().recv_timeout(Duration::from_millis(100)) {
                if let Some(handler) = self.handlers.lock().unwrap().get(&event.fd) {
                    handler(event);
                }
            }
        }

        println!("Reactor 事件循环结束");
    }

    /// 停止事件循环
    pub fn stop(&self) {
        *self.running.lock().unwrap() = false;
    }

    /// 尝试接收事件（用于演示）
    pub fn try_recv_event(&self) -> Option<IoEvent> {
        self.event_receiver.lock().unwrap().try_recv().ok()
    }
}

/// 简化版 epoll 模拟器
/// 
/// 实际实现会使用 Linux epoll 或类似机制
pub struct EpollSimulator {
    /// 注册的文件描述符和感兴趣的事件
    interests: Arc<Mutex<HashMap<RawFd, Vec<IoEventType>>>>,
    /// 事件通知发送端
    notifier: Option<Sender<IoEvent>>,
}

impl EpollSimulator {
    pub fn new() -> Self {
        Self {
            interests: Arc::new(Mutex::new(HashMap::new())),
            notifier: None,
        }
    }

    /// 关联 Reactor
    pub fn attach_reactor(&mut self, _reactor: &Reactor) {
        // 这里简化处理，直接使用 Reactor 的通道
    }

    /// 注册文件描述符
    pub fn add_interest(&self, fd: RawFd, events: Vec<IoEventType>) {
        self.interests.lock().unwrap().insert(fd, events);
    }

    /// 修改注册的事件
    pub fn modify_interest(&self, fd: RawFd, events: Vec<IoEventType>) {
        self.interests.lock().unwrap().insert(fd, events);
    }

    /// 删除注册的文件描述符
    pub fn remove_interest(&self, fd: RawFd) {
        self.interests.lock().unwrap().remove(&fd);
    }

    /// 模拟等待事件（在实际实现中这是 epoll_wait）
    pub fn wait(&self, timeout_ms: i32) -> Vec<IoEvent> {
        // 模拟：随机产生一些事件
        thread::sleep(Duration::from_millis(timeout_ms.max(0) as u64));
        
        let mut events = Vec::new();
        let interests = self.interests.lock().unwrap();
        
        // 模拟：为每个注册的文件描述符产生随机事件
        for (fd, event_types) in interests.iter() {
            if random_float() < 0.3 { // 30% 概率产生事件
                if let Some(event_type) = event_types.first() {
                    events.push(IoEvent {
                        fd: *fd,
                        event_type: *event_type,
                    });
                }
            }
        }
        
        events
    }
}

// 模拟随机数生成
fn random_float() -> f32 {
    use std::sync::atomic::{AtomicU32, Ordering};
    static SEED: AtomicU32 = AtomicU32::new(1);
    let mut seed = SEED.load(Ordering::Relaxed);
    seed = seed.wrapping_mul(1103515245).wrapping_add(12345);
    SEED.store(seed, Ordering::Relaxed);
    (seed as f32) / (u32::MAX as f32)
}

/// Proactor（主动器）模式
/// 
/// 与 Reactor 不同，Proactor 由操作系统完成IO操作后通知应用
pub struct Proactor {
    /// 待完成的IO操作队列
    pending_ops: Arc<Mutex<Vec<PendingOperation>>>,
    /// 完成通知通道
    completion_sender: Sender<CompletedOperation>,
    completion_receiver: Arc<Mutex<Receiver<CompletedOperation>>>,
}

/// 待完成的IO操作
#[derive(Debug)]
struct PendingOperation {
    id: u64,
    op_type: IoOperationType,
    start_time: Instant,
}

/// 完成的IO操作
#[derive(Debug)]
struct CompletedOperation {
    id: u64,
    result: IoResult,
}

/// IO操作类型
#[derive(Debug)]
enum IoOperationType {
    Read { fd: RawFd, buf_size: usize },
    Write { fd: RawFd, data: Vec<u8> },
}

/// IO操作结果
#[derive(Debug)]
enum IoResult {
    Success(Vec<u8>),
    Error(String),
    Timeout,
}

impl Proactor {
    pub fn new() -> Self {
        let (tx, rx) = channel();
        
        Self {
            pending_ops: Arc::new(Mutex::new(Vec::new())),
            completion_sender: tx,
            completion_receiver: Arc::new(Mutex::new(rx)),
        }
    }

    /// 提交异步读请求
    pub fn read(&self, fd: RawFd, buf_size: usize) -> u64 {
        let id = self.generate_id();
        let op = PendingOperation {
            id,
            op_type: IoOperationType::Read { fd, buf_size },
            start_time: Instant::now(),
        };
        
        self.pending_ops.lock().unwrap().push(op);
        
        // 模拟异步完成
        let sender = self.completion_sender.clone();
        thread::spawn(move || {
            thread::sleep(Duration::from_millis(100));
            let _ = sender.send(CompletedOperation {
                id,
                result: IoResult::Success(vec![0u8; buf_size]),
            });
        });
        
        id
    }

    /// 提交异步写请求
    pub fn write(&self, fd: RawFd, data: Vec<u8>) -> u64 {
        let id = self.generate_id();
        let op = PendingOperation {
            id,
            op_type: IoOperationType::Write { fd, data },
            start_time: Instant::now(),
        };
        
        self.pending_ops.lock().unwrap().push(op);
        
        let sender = self.completion_sender.clone();
        thread::spawn(move || {
            thread::sleep(Duration::from_millis(50));
            let _ = sender.send(CompletedOperation {
                id,
                result: IoResult::Success(vec![]),
            });
        });
        
        id
    }

    /// 等待操作完成
    pub fn wait_completion(&self, timeout: Duration) -> Option<CompletedOperation> {
        self.completion_receiver.lock().unwrap().recv_timeout(timeout).ok()
    }

    fn generate_id(&self) -> u64 {
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(1);
        COUNTER.fetch_add(1, Ordering::Relaxed)
    }
}

/// 异步IO调度器
/// 
/// 整合 Reactor 和 Proactor 模式
pub struct AsyncIoScheduler {
    reactor: Reactor,
    proactor: Proactor,
    epoll: EpollSimulator,
}

impl AsyncIoScheduler {
    pub fn new() -> Self {
        Self {
            reactor: Reactor::new(),
            proactor: Proactor::new(),
            epoll: EpollSimulator::new(),
        }
    }

    /// 设置TCP连接处理器
    pub fn setup_tcp_server(&self, port: u16) -> io::Result<()> {
        let _listener = TcpListener::bind(format!("127.0.0.1:{}", port))?;
        println!("TCP服务器监听端口 {}", port);
        let fd: RawFd = 0; // Windows下不使用实际fd
        
        // 注册接受连接处理器
        self.reactor.register(fd, move |event| {
            match event.event_type {
                IoEventType::Readable => {
                    println!("[Reactor] 新的连接请求 fd={}", event.fd);
                }
                IoEventType::Error => {
                    println!("[Reactor] 连接错误 fd={}", event.fd);
                }
                _ => {}
            }
        });
        
        Ok(())
    }

    /// 运行调度器（简化版）
    pub fn run(&self, duration_secs: u64) {
        println!("\n=== 异步IO调度器启动 ===");
        
        let start = Instant::now();
        
        // 模拟一些IO事件
        while start.elapsed().as_secs() < duration_secs {
            // 模拟 epoll_wait
            let events = self.epoll.wait(100);
            for event in events {
                self.reactor.send_event(event);
            }

            // 处理 Proactor 完成事件
            if let Some(completion) = self.proactor.wait_completion(Duration::from_millis(10)) {
                println!("[Proactor] 操作 {} 完成: {:?}", completion.id, completion.result);
            }
        }
        
        println!("=== 异步IO调度器停止 ===");
    }

    /// 执行异步读操作
    pub fn async_read(&self, fd: RawFd, size: usize) -> u64 {
        self.proactor.read(fd, size)
    }

    /// 执行异步写操作  
    pub fn async_write(&self, fd: RawFd, data: Vec<u8>) -> u64 {
        self.proactor.write(fd, data)
    }
}

/// IOCP (I/O Completion Port) 风格实现
/// Windows 下的高效异步IO机制
#[cfg(windows)]
pub mod iocp {
    use super::*;
    
    /// IOCP 结构
    pub struct IoCompletionPort {
        handle: isize, // HANDLE
    }
    
    impl IoCompletionPort {
        pub fn new() -> io::Result<Self> {
            // 实际实现需要调用 Windows API
            println!("创建 IOCP 对象");
            Ok(Self { handle: 0 })
        }
        
        pub fn associate_handle(&self, handle: RawFd, completion_key: usize) -> io::Result<()> {
            println!("关联句柄 {} 到 IOCP，key={}", handle, completion_key);
            Ok(())
        }
        
        pub fn get_completion_status(&self, timeout_ms: u32) -> io::Result<CompletionStatus> {
            // 模拟
            thread::sleep(Duration::from_millis(timeout_ms as u64));
            Ok(CompletionStatus {
                bytes_transferred: 1024,
                completion_key: 1,
                overlapped: std::ptr::null_mut(),
            })
        }
    }
    
    #[derive(Debug)]
    pub struct CompletionStatus {
        pub bytes_transferred: u32,
        pub completion_key: usize,
        pub overlapped: *mut (), // OVERLAPPED*
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reactor() {
        let reactor = Reactor::new();
        let counter = Arc::new(Mutex::new(0));
        
        let counter_clone = Arc::clone(&counter);
        reactor.register(1, move |event| {
            if event.event_type == IoEventType::Readable {
                *counter_clone.lock().unwrap() += 1;
            }
        });
        
        reactor.send_event(IoEvent {
            fd: 1,
            event_type: IoEventType::Readable,
        });
        
        // 由于事件循环是同步的，这里简化测试
        if let Some(handler) = reactor.handlers.lock().unwrap().get(&1) {
            handler(IoEvent {
                fd: 1,
                event_type: IoEventType::Readable,
            });
        }
        
        assert_eq!(*counter.lock().unwrap(), 1);
    }

    #[test]
    fn test_epoll_simulator() {
        let epoll = EpollSimulator::new();
        epoll.add_interest(1, vec![IoEventType::Readable]);
        epoll.add_interest(2, vec![IoEventType::Writable]);
        
        let events = epoll.wait(10);
        // 由于随机性，不检查具体事件数
        println!("产生 {} 个事件", events.len());
    }

    #[test]
    fn test_proactor() {
        let proactor = Proactor::new();
        
        let op_id = proactor.read(1, 1024);
        println!("提交读操作 {}", op_id);
        
        if let Some(completion) = proactor.wait_completion(Duration::from_millis(200)) {
            assert_eq!(completion.id, op_id);
        }
    }
}

fn main() {
    println!("=== 异步IO调度演示 ===\n");

    // Reactor 模式演示
    {
        println!("-- Reactor 模式 --");
        let reactor = Reactor::new();
        
        // 注册处理器
        reactor.register(1, |e| println!("处理器1: {:?}", e));
        reactor.register(2, |e| println!("处理器2: {:?}", e));
        
        // 模拟事件
        reactor.send_event(IoEvent { fd: 1, event_type: IoEventType::Readable });
        reactor.send_event(IoEvent { fd: 2, event_type: IoEventType::Writable });
        
        // 执行一次事件处理
        if let Some(event) = reactor.try_recv_event() {
            if let Some(handler) = reactor.handlers.lock().unwrap().get(&event.fd) {
                handler(event);
            }
        }
    }

    // Epoll 演示
    {
        println!("\n-- Epoll 模拟器 --");
        let epoll = EpollSimulator::new();
        
        epoll.add_interest(1, vec![IoEventType::Readable, IoEventType::Error]);
        epoll.add_interest(2, vec![IoEventType::Writable]);
        epoll.add_interest(3, vec![IoEventType::Readable]);
        
        let events = epoll.wait(100);
        println!("等待返回 {} 个事件:", events.len());
        for event in events {
            println!("  fd={}, type={:?}", event.fd, event.event_type);
        }
    }

    // Proactor 演示
    {
        println!("\n-- Proactor 模式 --");
        let proactor = Proactor::new();
        
        let read_id = proactor.read(1, 1024);
        let write_id = proactor.write(2, vec![1, 2, 3, 4, 5]);
        
        println!("提交异步读操作: {}", read_id);
        println!("提交异步写操作: {}", write_id);
        
        // 等待完成
        while let Some(completion) = proactor.wait_completion(Duration::from_millis(200)) {
            println!("操作 {} 完成", completion.id);
            if completion.id == write_id {
                break;
            }
        }
    }

    println!("\n=== 演示完成 ===");
}
