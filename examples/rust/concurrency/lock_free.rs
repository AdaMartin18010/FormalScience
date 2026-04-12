/// 无锁数据结构实现
/// 
/// 演示无锁队列、RCU (Read-Copy-Update) 等无锁并发模式

use std::sync::atomic::{fence, AtomicPtr, AtomicUsize, Ordering};
use std::ptr::null_mut;
use std::sync::Arc;
use std::thread;
use std::time::Duration;

// ============== 无锁栈 (Treiber Stack) ==============

/// 无锁栈节点
struct Node<T> {
    data: T,
    next: AtomicPtr<Node<T>>,
}

/// Treiber 无锁栈
/// 
/// 使用 CAS (Compare-And-Swap) 实现线程安全的栈
pub struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
    len: AtomicUsize,
}

impl<T> LockFreeStack<T> {
    /// 创建新的无锁栈
    pub fn new() -> Self {
        Self {
            head: AtomicPtr::new(null_mut()),
            len: AtomicUsize::new(0),
        }
    }

    /// 压入元素（无锁）
    pub fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: AtomicPtr::new(null_mut()),
        }));

        loop {
            // 获取当前头节点
            let head = self.head.load(Ordering::Relaxed);
            
            // 设置新节点的 next 指向当前头节点
            unsafe {
                (*new_node).next.store(head, Ordering::Relaxed);
            }
            
            // 尝试 CAS 更新头节点
            match self.head.compare_exchange_weak(
                head,
                new_node,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    self.len.fetch_add(1, Ordering::Relaxed);
                    break;
                }
                Err(_) => {
                    // CAS 失败，重试
                    std::hint::spin_loop();
                }
            }
        }
    }

    /// 弹出元素（无锁）
    pub fn pop(&self) -> Option<T> {
        loop {
            // 获取当前头节点
            let head = self.head.load(Ordering::Acquire);
            
            if head.is_null() {
                return None;
            }
            
            // 获取下一个节点
            let next = unsafe { (*head).next.load(Ordering::Relaxed) };
            
            // 尝试 CAS 更新头节点
            match self.head.compare_exchange_weak(
                head,
                next,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    self.len.fetch_sub(1, Ordering::Relaxed);
                    
                    // 获取数据并释放节点
                    unsafe {
                        let node = Box::from_raw(head);
                        return Some(node.data);
                    }
                }
                Err(_) => {
                    // CAS 失败，重试
                    std::hint::spin_loop();
                }
            }
        }
    }

    /// 获取栈大小
    pub fn len(&self) -> usize {
        self.len.load(Ordering::Relaxed)
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> Drop for LockFreeStack<T> {
    fn drop(&mut self) {
        // 释放所有剩余节点
        while self.pop().is_some() {}
    }
}

unsafe impl<T: Send> Send for LockFreeStack<T> {}
unsafe impl<T: Send> Sync for LockFreeStack<T> {}

// ============== 无锁队列 (Michael-Scott Queue) ==============

/// 队列节点
struct QueueNode<T> {
    data: Option<T>,
    next: AtomicPtr<QueueNode<T>>,
}

/// Michael-Scott 无锁队列
/// 
/// 经典的基于链表的无锁队列算法
pub struct LockFreeQueue<T> {
    head: AtomicPtr<QueueNode<T>>,
    tail: AtomicPtr<QueueNode<T>>,
    len: AtomicUsize,
}

impl<T> LockFreeQueue<T> {
    /// 创建新的无锁队列
    pub fn new() -> Self {
        // 创建哨兵节点
        let sentinel = Box::into_raw(Box::new(QueueNode {
            data: None,
            next: AtomicPtr::new(null_mut()),
        }));

        Self {
            head: AtomicPtr::new(sentinel),
            tail: AtomicPtr::new(sentinel),
            len: AtomicUsize::new(0),
        }
    }

    /// 入队操作
    pub fn enqueue(&self, data: T) {
        let new_node = Box::into_raw(Box::new(QueueNode {
            data: Some(data),
            next: AtomicPtr::new(null_mut()),
        }));

        loop {
            // 获取当前尾节点
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*tail).next.load(Ordering::Acquire) };

            // 检查尾节点是否仍然有效
            if tail == self.tail.load(Ordering::Acquire) {
                if next.is_null() {
                    // 尝试链接新节点
                    if unsafe {
                        (*tail)
                            .next
                            .compare_exchange_weak(
                                next,
                                new_node,
                                Ordering::Release,
                                Ordering::Relaxed,
                            )
                            .is_ok()
                    } {
                        // 尝试更新尾指针
                        let _ = self.tail.compare_exchange(
                            tail,
                            new_node,
                            Ordering::Release,
                            Ordering::Relaxed,
                        );
                        self.len.fetch_add(1, Ordering::Relaxed);
                        break;
                    }
                } else {
                    // 尾节点落后，尝试更新尾指针
                    let _ = self.tail.compare_exchange(
                        tail,
                        next,
                        Ordering::Release,
                        Ordering::Relaxed,
                    );
                }
            }
        }
    }

    /// 出队操作
    pub fn dequeue(&self) -> Option<T> {
        loop {
            // 获取头节点和尾节点
            let head = self.head.load(Ordering::Acquire);
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*head).next.load(Ordering::Acquire) };

            // 检查头节点是否仍然有效
            if head == self.head.load(Ordering::Acquire) {
                if head == tail {
                    // 队列为空或尾节点落后
                    if next.is_null() {
                        return None;
                    }
                    // 尝试更新尾指针
                    let _ = self.tail.compare_exchange(
                        tail,
                        next,
                        Ordering::Release,
                        Ordering::Relaxed,
                    );
                } else {
                    // 获取数据
                    let data = unsafe { (*next).data.take() };
                    
                    // 尝试更新头指针
                    if self
                        .head
                        .compare_exchange_weak(
                            head,
                            next,
                            Ordering::Release,
                            Ordering::Relaxed,
                        )
                        .is_ok()
                    {
                        // 释放旧的头节点（哨兵节点）
                        unsafe {
                            let _ = Box::from_raw(head);
                        }
                        self.len.fetch_sub(1, Ordering::Relaxed);
                        return data;
                    }
                }
            }
        }
    }

    /// 获取队列长度
    pub fn len(&self) -> usize {
        self.len.load(Ordering::Relaxed)
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> Drop for LockFreeQueue<T> {
    fn drop(&mut self) {
        // 释放所有节点
        while self.dequeue().is_some() {}
        
        // 释放最后的哨兵节点
        let head = self.head.load(Ordering::Relaxed);
        if !head.is_null() {
            unsafe {
                let _ = Box::from_raw(head);
            }
        }
    }
}

unsafe impl<T: Send> Send for LockFreeQueue<T> {}
unsafe impl<T: Send> Sync for LockFreeQueue<T> {}

// ============== RCU (Read-Copy-Update) ==============

/// RCU 保护的数据
/// 
/// 实现简单的 RCU 机制，适用于读多写少的场景
pub struct Rcu<T> {
    ptr: AtomicPtr<T>,
}

impl<T: Clone> Rcu<T> {
    /// 创建新的 RCU 实例
    pub fn new(data: T) -> Self {
        let ptr = Box::into_raw(Box::new(data));
        Self {
            ptr: AtomicPtr::new(ptr),
        }
    }

    /// 读取数据（无锁，高性能）
    /// 
    /// 返回的数据指针在读取期间有效，但不保证在读取后仍然有效
    pub fn read(&self) -> &T {
        let ptr = self.ptr.load(Ordering::Acquire);
        unsafe { &*ptr }
    }

    /// 更新数据（Copy-on-Write）
    /// 
    /// 创建数据的副本，修改后原子更新指针
    pub fn update<F>(&self, f: F)
    where
        F: FnOnce(&mut T),
    {
        // 获取当前指针
        let old_ptr = self.ptr.load(Ordering::Acquire);
        
        // 创建副本
        let mut new_data = unsafe { (*old_ptr).clone() };
        f(&mut new_data);
        
        // 将新数据放入堆
        let new_ptr = Box::into_raw(Box::new(new_data));
        
        // 原子更新指针
        self.ptr.store(new_ptr, Ordering::Release);
        
        // 内存屏障，确保之前的写操作完成
        fence(Ordering::SeqCst);
        
        // 注意：实际的 RCU 实现需要等待所有读者完成（宽限期）
        // 这里简化处理，延迟释放旧数据
        unsafe {
            // 在实际实现中，这里应该将旧数据加入待释放队列
            // 等待宽限期后再释放
            let _ = Box::from_raw(old_ptr);
        }
    }
}

impl<T: Clone> Rcu<T> {
    /// 获取数据的克隆
    pub fn get(&self) -> T {
        self.read().clone()
    }
}

impl<T> Drop for Rcu<T> {
    fn drop(&mut self) {
        let ptr = self.ptr.load(Ordering::Relaxed);
        if !ptr.is_null() {
            unsafe {
                let _ = Box::from_raw(ptr);
            }
        }
    }
}

unsafe impl<T: Send> Send for Rcu<T> {}
unsafe impl<T: Send + Sync> Sync for Rcu<T> {}

// ============== 无锁计数器 ==============

/// 无锁计数器
pub struct AtomicCounter {
    value: AtomicUsize,
}

impl AtomicCounter {
    pub fn new(initial: usize) -> Self {
        Self {
            value: AtomicUsize::new(initial),
        }
    }

    /// 增加计数
    pub fn increment(&self) -> usize {
        self.value.fetch_add(1, Ordering::Relaxed)
    }

    /// 减少计数
    pub fn decrement(&self) -> usize {
        self.value.fetch_sub(1, Ordering::Relaxed)
    }

    /// 获取当前值
    pub fn get(&self) -> usize {
        self.value.load(Ordering::Relaxed)
    }

    /// CAS 更新
    pub fn compare_and_swap(&self, current: usize, new: usize) -> Result<usize, usize> {
        match self.value.compare_exchange(
            current,
            new,
            Ordering::SeqCst,
            Ordering::Relaxed,
        ) {
            Ok(_) => Ok(new),
            Err(actual) => Err(actual),
        }
    }
}

// ============== 使用示例 ==============

fn demo_lock_free_stack() {
    println!("\n=== 无锁栈演示 ===");
    
    let stack = Arc::new(LockFreeStack::new());
    let mut handles = vec![];
    
    // 多个生产者
    for i in 0..3 {
        let stack = Arc::clone(&stack);
        handles.push(thread::spawn(move || {
            for j in 0..5 {
                stack.push(i * 10 + j);
            }
        }));
    }
    
    // 多个消费者
    for i in 0..2 {
        let stack = Arc::clone(&stack);
        handles.push(thread::spawn(move || {
            for _ in 0..5 {
                if let Some(val) = stack.pop() {
                    println!("消费者 {} 弹出: {}", i, val);
                }
            }
        }));
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("栈中剩余元素: {}", stack.len());
}

fn demo_lock_free_queue() {
    println!("\n=== 无锁队列演示 ===");
    
    let queue = Arc::new(LockFreeQueue::new());
    let mut handles = vec![];
    
    // 生产者
    for i in 0..2 {
        let queue = Arc::clone(&queue);
        handles.push(thread::spawn(move || {
            for j in 0..5 {
                queue.enqueue(i * 10 + j);
                println!("生产者 {} 入队: {}", i, i * 10 + j);
            }
        }));
    }
    
    thread::sleep(Duration::from_millis(100));
    
    // 消费者
    for i in 0..2 {
        let queue = Arc::clone(&queue);
        handles.push(thread::spawn(move || {
            for _ in 0..5 {
                if let Some(val) = queue.dequeue() {
                    println!("消费者 {} 出队: {}", i, val);
                }
            }
        }));
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("队列中剩余元素: {}", queue.len());
}

fn demo_rcu() {
    println!("\n=== RCU 演示 ===");
    
    let rcu = Arc::new(Rcu::new(vec![1, 2, 3]));
    
    // 读者线程
    let rcu_read = Arc::clone(&rcu);
    let reader = thread::spawn(move || {
        for i in 0..10 {
            let data = rcu_read.get();
            println!("读者 {} 读取: {:?}", i, data);
            thread::sleep(Duration::from_millis(10));
        }
    });
    
    // 写者线程
    let rcu_write = Arc::clone(&rcu);
    let writer = thread::spawn(move || {
        for i in 0..5 {
            rcu_write.update(|v| v.push(i + 10));
            println!("写者 {} 更新数据", i);
            thread::sleep(Duration::from_millis(20));
        }
    });
    
    reader.join().unwrap();
    writer.join().unwrap();
    
    println!("最终数据: {:?}", rcu.get());
}

fn demo_atomic_counter() {
    println!("\n=== 无锁计数器演示 ===");
    
    let counter = Arc::new(AtomicCounter::new(0));
    let mut handles = vec![];
    
    for i in 0..5 {
        let counter = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            for _ in 0..1000 {
                counter.increment();
            }
            println!("线程 {} 完成", i);
        }));
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("最终计数: {}", counter.get());
    assert_eq!(counter.get(), 5000);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lock_free_stack() {
        let stack = LockFreeStack::new();
        
        stack.push(1);
        stack.push(2);
        stack.push(3);
        
        assert_eq!(stack.pop(), Some(3));
        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.len(), 1);
    }

    #[test]
    fn test_lock_free_stack_concurrent() {
        let stack = Arc::new(LockFreeStack::new());
        let mut handles = vec![];
        
        for _ in 0..10 {
            let stack = Arc::clone(&stack);
            handles.push(thread::spawn(move || {
                for i in 0..100 {
                    stack.push(i);
                }
            }));
        }
        
        for h in handles {
            h.join().unwrap();
        }
        
        assert_eq!(stack.len(), 1000);
    }

    #[test]
    fn test_lock_free_queue() {
        let queue = LockFreeQueue::new();
        
        queue.enqueue(1);
        queue.enqueue(2);
        queue.enqueue(3);
        
        assert_eq!(queue.dequeue(), Some(1));
        assert_eq!(queue.dequeue(), Some(2));
        assert_eq!(queue.len(), 1);
    }

    #[test]
    fn test_rcu() {
        let rcu = Rcu::new(42);
        
        assert_eq!(*rcu.read(), 42);
        
        rcu.update(|v| *v = 100);
        assert_eq!(*rcu.read(), 100);
    }

    #[test]
    fn test_atomic_counter() {
        let counter = AtomicCounter::new(0);
        
        counter.increment();
        counter.increment();
        assert_eq!(counter.get(), 2);
        
        counter.decrement();
        assert_eq!(counter.get(), 1);
    }
}

fn main() {
    println!("=== 无锁数据结构演示 ===");
    
    demo_lock_free_stack();
    demo_lock_free_queue();
    demo_rcu();
    demo_atomic_counter();
    
    println!("\n=== 演示完成 ===");
}
