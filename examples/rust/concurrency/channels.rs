/// 通道 (Channel) 实现
/// 
/// 演示 MPSC (多生产者单消费者)、广播通道等并发通信模式

use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

// ============== MPSC 通道 ==============

/// MPSC 通道内部结构
struct ChannelInner<T> {
    /// 消息队列
    queue: VecDeque<T>,
    /// 发送端是否全部关闭
    sender_closed: bool,
}

/// MPSC 发送端
pub struct Sender<T> {
    inner: Arc<(Mutex<ChannelInner<T>>, Condvar)>,
    /// 引用计数，用于判断是否所有发送端都关闭
    sender_count: Arc<AtomicUsize>,
}

impl<T> Sender<T> {
    /// 发送消息
    pub fn send(&self, msg: T) -> Result<(), SendError<T>> {
        let (lock, cvar) = &*self.inner;
        let mut inner = lock.lock().unwrap();
        
        if inner.sender_closed {
            return Err(SendError(msg));
        }
        
        inner.queue.push_back(msg);
        cvar.notify_one();
        
        Ok(())
    }

    /// 检查接收端是否还在
    pub fn is_connected(&self) -> bool {
        Arc::strong_count(&self.inner) > 1
    }
}

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Self {
        self.sender_count.fetch_add(1, Ordering::Relaxed);
        Self {
            inner: Arc::clone(&self.inner),
            sender_count: Arc::clone(&self.sender_count),
        }
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        let count = self.sender_count.fetch_sub(1, Ordering::Relaxed);
        if count == 1 {
            // 最后一个发送端关闭
            let (lock, cvar) = &*self.inner;
            let mut inner = lock.lock().unwrap();
            inner.sender_closed = true;
            cvar.notify_one();
        }
    }
}

/// MPSC 接收端
pub struct Receiver<T> {
    inner: Arc<(Mutex<ChannelInner<T>>, Condvar)>,
}

impl<T> Receiver<T> {
    /// 接收消息（阻塞）
    pub fn recv(&self) -> Result<T, RecvError> {
        let (lock, cvar) = &*self.inner;
        let mut inner = lock.lock().unwrap();
        
        loop {
            if let Some(msg) = inner.queue.pop_front() {
                return Ok(msg);
            }
            
            if inner.sender_closed {
                return Err(RecvError);
            }
            
            // 等待消息
            inner = cvar.wait(inner).unwrap();
        }
    }

    /// 尝试接收消息（非阻塞）
    pub fn try_recv(&self) -> Result<T, TryRecvError> {
        let (lock, _) = &*self.inner;
        let mut inner = lock.lock().unwrap();
        
        if let Some(msg) = inner.queue.pop_front() {
            return Ok(msg);
        }
        
        if inner.sender_closed {
            Err(TryRecvError::Disconnected)
        } else {
            Err(TryRecvError::Empty)
        }
    }

    /// 接收消息（带超时）
    pub fn recv_timeout(&self, timeout: Duration) -> Result<T, RecvTimeoutError> {
        let (lock, cvar) = &*self.inner;
        let mut inner = lock.lock().unwrap();
        let deadline = std::time::Instant::now() + timeout;
        
        loop {
            if let Some(msg) = inner.queue.pop_front() {
                return Ok(msg);
            }
            
            if inner.sender_closed {
                return Err(RecvTimeoutError::Disconnected);
            }
            
            let now = std::time::Instant::now();
            if now >= deadline {
                return Err(RecvTimeoutError::Timeout);
            }
            
            let remaining = deadline - now;
            let result = cvar.wait_timeout(inner, remaining).unwrap();
            inner = result.0;
        }
    }

    /// 创建迭代器
    pub fn iter(&self) -> Iter<T> {
        Iter { rx: self }
    }
}

impl<T> Iterator for Receiver<T> {
    type Item = T;
    
    fn next(&mut self) -> Option<Self::Item> {
        self.recv().ok()
    }
}

/// 接收端迭代器
pub struct Iter<'a, T> {
    rx: &'a Receiver<T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = T;
    
    fn next(&mut self) -> Option<Self::Item> {
        self.rx.recv().ok()
    }
}

/// 错误类型
pub struct SendError<T>(pub T);

impl<T> std::fmt::Debug for SendError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SendError")
    }
}

#[derive(Debug)]
pub struct RecvError;

#[derive(Debug)]
pub enum TryRecvError {
    Empty,
    Disconnected,
}

#[derive(Debug)]
pub enum RecvTimeoutError {
    Timeout,
    Disconnected,
}

/// 创建 MPSC 通道
pub fn channel<T>() -> (Sender<T>, Receiver<T>) {
    let inner = Arc::new((
        Mutex::new(ChannelInner {
            queue: VecDeque::new(),
            sender_closed: false,
        }),
        Condvar::new(),
    ));
    
    let sender_count = Arc::new(AtomicUsize::new(1));
    
    (
        Sender {
            inner: Arc::clone(&inner),
            sender_count,
        },
        Receiver { inner },
    )
}

// ============== 有界通道 (Bounded Channel) ==============

/// 有界通道内部结构
struct BoundedChannelInner<T> {
    queue: VecDeque<T>,
    capacity: usize,
    sender_closed: bool,
}

/// 有界通道发送端
pub struct BoundedSender<T> {
    inner: Arc<(Mutex<BoundedChannelInner<T>>, Condvar, Condvar)>,
}

impl<T> BoundedSender<T> {
    /// 发送消息（如果满则阻塞）
    pub fn send(&self, msg: T) -> Result<(), SendError<T>> {
        let (lock, not_full, not_empty) = &*self.inner;
        let mut inner = lock.lock().unwrap();
        
        // 等待队列不满
        while inner.queue.len() >= inner.capacity {
            if inner.sender_closed {
                return Err(SendError(msg));
            }
            inner = not_full.wait(inner).unwrap();
        }
        
        inner.queue.push_back(msg);
        not_empty.notify_one();
        
        Ok(())
    }

    /// 尝试发送（非阻塞）
    pub fn try_send(&self, msg: T) -> Result<(), TrySendError<T>> {
        let (lock, _, not_empty) = &*self.inner;
        let mut inner = lock.lock().unwrap();
        
        if inner.sender_closed {
            return Err(TrySendError::Disconnected(msg));
        }
        
        if inner.queue.len() >= inner.capacity {
            return Err(TrySendError::Full(msg));
        }
        
        inner.queue.push_back(msg);
        not_empty.notify_one();
        
        Ok(())
    }
}

impl<T> Clone for BoundedSender<T> {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl<T> Drop for BoundedSender<T> {
    fn drop(&mut self) {
        // 简化处理：实际应该检查引用计数
    }
}

/// 有界通道接收端
pub struct BoundedReceiver<T> {
    inner: Arc<(Mutex<BoundedChannelInner<T>>, Condvar, Condvar)>,
}

impl<T> BoundedReceiver<T> {
    /// 接收消息
    pub fn recv(&self) -> Result<T, RecvError> {
        let (lock, not_full, not_empty) = &*self.inner;
        let mut inner = lock.lock().unwrap();
        
        loop {
            if let Some(msg) = inner.queue.pop_front() {
                not_full.notify_one();
                return Ok(msg);
            }
            
            if inner.sender_closed {
                return Err(RecvError);
            }
            
            inner = not_empty.wait(inner).unwrap();
        }
    }
}

/// 有界通道发送错误
#[derive(Debug)]
pub enum TrySendError<T> {
    Full(T),
    Disconnected(T),
}

/// 创建有界通道
pub fn bounded_channel<T>(capacity: usize) -> (BoundedSender<T>, BoundedReceiver<T>) {
    let inner = Arc::new((
        Mutex::new(BoundedChannelInner {
            queue: VecDeque::new(),
            capacity,
            sender_closed: false,
        }),
        Condvar::new(), // not_full
        Condvar::new(), // not_empty
    ));
    
    (
        BoundedSender {
            inner: Arc::clone(&inner),
        },
        BoundedReceiver { inner },
    )
}

// ============== 广播通道 (Broadcast Channel) ==============

/// 广播消息
struct BroadcastMessage<T> {
    data: T,
    /// 剩余接收者数量
    receivers: AtomicUsize,
}

/// 广播发送端
pub struct BroadcastSender<T> {
    /// 订阅者列表
    subscribers: Arc<Mutex<Vec<Sender<T>>>>,
    /// 下一个订阅者ID
    next_id: AtomicUsize,
}

impl<T: Clone> BroadcastSender<T> {
    /// 广播消息给所有订阅者
    pub fn broadcast(&self, msg: T) -> Result<usize, BroadcastError> {
        let subscribers = self.subscribers.lock().unwrap();
        let mut sent = 0;
        
        for tx in subscribers.iter() {
            if tx.send(msg.clone()).is_ok() {
                sent += 1;
            }
        }
        
        if sent == 0 && !subscribers.is_empty() {
            Err(BroadcastError::AllDisconnected)
        } else {
            Ok(sent)
        }
    }

    /// 创建新的订阅者
    pub fn subscribe(&self) -> Receiver<T> {
        let (tx, rx) = channel();
        self.subscribers.lock().unwrap().push(tx);
        rx
    }
}

impl<T> Clone for BroadcastSender<T> {
    fn clone(&self) -> Self {
        Self {
            subscribers: Arc::clone(&self.subscribers),
            next_id: AtomicUsize::new(0),
        }
    }
}

/// 广播接收端
pub struct BroadcastReceiver<T> {
    inner: Receiver<T>,
}

impl<T> BroadcastReceiver<T> {
    pub fn recv(&self) -> Result<T, RecvError> {
        self.inner.recv()
    }
}

#[derive(Debug)]
pub enum BroadcastError {
    AllDisconnected,
}

/// 创建广播通道
pub fn broadcast_channel<T>() -> (BroadcastSender<T>, BroadcastReceiver<T>) {
    let (tx, rx) = channel();
    
    let sender = BroadcastSender {
        subscribers: Arc::new(Mutex::new(vec![tx])),
        next_id: AtomicUsize::new(1),
    };
    
    let receiver = BroadcastReceiver { inner: rx };
    
    (sender, receiver)
}

// ============== Select 多路复用 ==============

/// 选择操作结果
pub enum SelectResult<T> {
    Data(T),
    Closed,
    WouldBlock,
}

/// 简单的 select 宏模拟
/// 
/// 在实际项目中应使用 crossbeam-channel 或 tokio::select!
#[macro_export]
macro_rules! select {
    (
        $recv:ident = $ch:expr => $body:tt,
        default => $default_body:tt
    ) => {
        match $ch.try_recv() {
            Ok($recv) => $body,
            Err(TryRecvError::Disconnected) => { let $recv = None; $body }
            Err(TryRecvError::Empty) => $default_body,
        }
    };
}

// ============== 使用示例 ==============

fn demo_mpsc() {
    println!("\n=== MPSC 通道演示 ===");
    
    let (tx, rx) = channel::<i32>();
    let mut handles = vec![];
    
    // 多个生产者
    for i in 0..3 {
        let tx = tx.clone();
        handles.push(thread::spawn(move || {
            for j in 0..5 {
                tx.send(i * 100 + j).unwrap();
            }
        }));
    }
    
    // 释放原始发送端，只保留克隆的
    drop(tx);
    
    // 单消费者
    let consumer = thread::spawn(move || {
        let mut count = 0;
        while let Ok(msg) = rx.recv() {
            println!("接收: {}", msg);
            count += 1;
            if count >= 10 {
                break;
            }
        }
    });
    
    for handle in handles {
        handle.join().unwrap();
    }
    consumer.join().unwrap();
}

fn demo_bounded_channel() {
    println!("\n=== 有界通道演示 ===");
    
    let (tx, rx) = bounded_channel::<String>(3);
    
    // 生产者
    let producer = thread::spawn(move || {
        for i in 0..5 {
            let msg = format!("消息 {}", i);
            println!("发送: {}", msg);
            tx.send(msg).unwrap();
            thread::sleep(Duration::from_millis(50));
        }
    });
    
    // 慢速消费者
    let consumer = thread::spawn(move || {
        loop {
            match rx.recv() {
                Ok(msg) => {
                    println!("接收: {}", msg);
                    thread::sleep(Duration::from_millis(100));
                }
                Err(_) => break,
            }
        }
    });
    
    producer.join().unwrap();
    consumer.join().unwrap();
}

fn demo_broadcast() {
    println!("\n=== 广播通道演示 ===");
    
    let (tx, _rx) = broadcast_channel::<String>();
    
    // 创建多个订阅者
    let rx1 = tx.subscribe();
    let rx2 = tx.subscribe();
    let rx3 = tx.subscribe();
    
    // 广播者
    let broadcaster = thread::spawn(move || {
        for i in 0..5 {
            let msg = format!("广播 {}", i);
            let count = tx.broadcast(msg.clone()).unwrap();
            println!("广播 '{}' 给 {} 个接收者", msg, count);
            thread::sleep(Duration::from_millis(100));
        }
    });
    
    // 多个接收者
    let mut handles = vec![];
    for (idx, rx) in [rx1, rx2, rx3].into_iter().enumerate() {
        handles.push(thread::spawn(move || {
            loop {
                match rx.recv() {
                    Ok(msg) => println!("接收者 {} 收到: {}", idx, msg),
                    Err(_) => {
                        println!("接收者 {} 断开", idx);
                        break;
                    }
                }
            }
        }));
    }
    
    broadcaster.join().unwrap();
    for handle in handles {
        handle.join().unwrap();
    }
}

fn demo_channel_patterns() {
    println!("\n=== 通道模式演示 ===");
    
    // 工作队列模式
    println!("-- 工作队列模式 --");
    let (work_tx, work_rx) = channel::<Box<dyn FnOnce() + Send>>();
    
    let worker = thread::spawn(move || {
        while let Ok(job) = work_rx.recv() {
            job();
        }
    });
    
    work_tx.send(Box::new(|| println!("执行任务 1"))).unwrap();
    work_tx.send(Box::new(|| println!("执行任务 2"))).unwrap();
    
    drop(work_tx);
    worker.join().unwrap();
    
    // 结果通道模式
    println!("\n-- 结果通道模式 --");
    let (request_tx, request_rx) = channel::<(i32, Sender<i32>)>();
    
    let processor = thread::spawn(move || {
        while let Ok((num, result_tx)) = request_rx.recv() {
            let result = num * num;
            result_tx.send(result).unwrap();
        }
    });
    
    let (result_tx, result_rx) = channel();
    let _ = request_tx.send((5, result_tx));
    
    if let Ok(result) = result_rx.recv() {
        println!("5^2 = {}", result);
    }
    
    drop(request_tx);
    processor.join().unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_channel_basic() {
        let (tx, rx) = channel::<i32>();
        
        tx.send(1).unwrap();
        tx.send(2).unwrap();
        tx.send(3).unwrap();
        
        assert_eq!(rx.recv().unwrap(), 1);
        assert_eq!(rx.recv().unwrap(), 2);
        assert_eq!(rx.recv().unwrap(), 3);
    }

    #[test]
    fn test_channel_multi_sender() {
        let (tx, rx) = channel::<i32>();
        
        let tx1 = tx.clone();
        let tx2 = tx.clone();
        
        tx1.send(1).unwrap();
        tx2.send(2).unwrap();
        tx.send(3).unwrap();
        
        let mut received = vec![];
        for _ in 0..3 {
            received.push(rx.recv().unwrap());
        }
        
        received.sort();
        assert_eq!(received, vec![1, 2, 3]);
    }

    #[test]
    fn test_bounded_channel() {
        let (tx, rx) = bounded_channel::<i32>(2);
        
        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();
        
        // 应该满
        assert!(matches!(tx.try_send(3), Err(TrySendError::Full(3))));
        
        assert_eq!(rx.recv().unwrap(), 1);
        assert_eq!(rx.recv().unwrap(), 2);
    }

    #[test]
    fn test_broadcast() {
        let (tx, _) = broadcast_channel::<i32>();
        
        let rx1 = tx.subscribe();
        let rx2 = tx.subscribe();
        
        tx.broadcast(42).unwrap();
        
        assert_eq!(rx1.recv().unwrap(), 42);
        assert_eq!(rx2.recv().unwrap(), 42);
    }

    #[test]
    fn test_try_recv() {
        let (tx, rx) = channel::<i32>();
        
        // 空
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
        
        tx.send(1).unwrap();
        assert_eq!(rx.try_recv().unwrap(), 1);
        
        drop(tx);
        // 断开
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Disconnected)));
    }
}

fn main() {
    println!("=== 通道演示 ===");
    
    demo_mpsc();
    demo_bounded_channel();
    demo_broadcast();
    demo_channel_patterns();
    
    println!("\n=== 演示完成 ===");
}
