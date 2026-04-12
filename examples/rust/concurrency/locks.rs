/// 锁机制实现
/// 
/// 演示互斥锁(Mutex)、读写锁(RwLock)和自旋锁(SpinLock)的实现和使用

use std::cell::UnsafeCell;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{fence, AtomicBool, AtomicU32, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

// ============== 自旋锁实现 ==============

/// 自旋锁结构
/// 
/// 自旋锁是一种忙等待锁，适用于锁持有时间很短的场景
pub struct SpinLock<T> {
    locked: AtomicBool,
    data: UnsafeCell<T>,
}

/// 自旋锁守卫
pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

// SpinLock 是 Sync 的，因为我们可以安全地在多个线程间共享
unsafe impl<T: Send> Sync for SpinLock<T> {}
unsafe impl<T: Send> Send for SpinLock<T> {}

impl<T> SpinLock<T> {
    /// 创建新的自旋锁
    pub const fn new(data: T) -> Self {
        Self {
            locked: AtomicBool::new(false),
            data: UnsafeCell::new(data),
        }
    }

    /// 获取锁（自旋等待）
    pub fn lock(&self) -> SpinLockGuard<T> {
        // 自旋等待，直到成功获取锁
        while self.locked.compare_exchange_weak(
            false,
            true,
            Ordering::Acquire,
            Ordering::Relaxed
        ).is_err() {
            // 提示CPU我们在自旋，减少功耗
            std::hint::spin_loop();
        }
        
        SpinLockGuard { lock: self }
    }

    /// 尝试获取锁（非阻塞）
    pub fn try_lock(&self) -> Option<SpinLockGuard<T>> {
        if self.locked.compare_exchange(
            false,
            true,
            Ordering::Acquire,
            Ordering::Relaxed
        ).is_ok() {
            Some(SpinLockGuard { lock: self })
        } else {
            None
        }
    }

    /// 释放锁
    fn unlock(&self) {
        self.locked.store(false, Ordering::Release);
    }
}

impl<'a, T> Deref for SpinLockGuard<'a, T> {
    type Target = T;
    
    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<'a, T> DerefMut for SpinLockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<'a, T> Drop for SpinLockGuard<'a, T> {
    fn drop(&mut self) {
        self.lock.unlock();
    }
}

// ============== 读写锁实现 ==============

/// 读写锁状态
const READER: u32 = 1 << 30;        // 读计数基数
const WRITER: u32 = 1 << 31;        // 写锁标志
const MAX_READERS: u32 = READER - 1; // 最大读者数

/// 读写锁
/// 
/// 允许多个读者同时访问，或一个写者独占访问
pub struct RwLock<T> {
    // 高1位: 写锁标志
    // 次1位: 读锁标志
    // 低30位: 等待的读者数
    state: AtomicU32,
    data: UnsafeCell<T>,
}

/// 读锁守卫
pub struct RwLockReadGuard<'a, T> {
    lock: &'a RwLock<T>,
}

/// 写锁守卫
pub struct RwLockWriteGuard<'a, T> {
    lock: &'a RwLock<T>,
}

unsafe impl<T: Send> Sync for RwLock<T> {}
unsafe impl<T: Send> Send for RwLock<T> {}

impl<T> RwLock<T> {
    /// 创建新的读写锁
    pub const fn new(data: T) -> Self {
        Self {
            state: AtomicU32::new(0),
            data: UnsafeCell::new(data),
        }
    }

    /// 获取读锁
    pub fn read(&self) -> RwLockReadGuard<T> {
        loop {
            let state = self.state.load(Ordering::Relaxed);
            
            // 检查是否有写者
            if state & WRITER != 0 {
                std::hint::spin_loop();
                continue;
            }
            
            // 尝试增加读者计数
            let new_state = state + 1;
            if new_state > MAX_READERS {
                panic!("读锁溢出");
            }
            
            if self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::Acquire,
                Ordering::Relaxed
            ).is_ok() {
                break;
            }
            
            std::hint::spin_loop();
        }
        
        RwLockReadGuard { lock: self }
    }

    /// 获取写锁
    pub fn write(&self) -> RwLockWriteGuard<T> {
        loop {
            let state = self.state.load(Ordering::Relaxed);
            
            // 检查是否已经有读者或写者
            if state != 0 {
                std::hint::spin_loop();
                continue;
            }
            
            // 尝试获取写锁
            if self.state.compare_exchange_weak(
                state,
                WRITER,
                Ordering::Acquire,
                Ordering::Relaxed
            ).is_ok() {
                break;
            }
            
            std::hint::spin_loop();
        }
        
        RwLockWriteGuard { lock: self }
    }

    /// 释放读锁
    fn unlock_read(&self) {
        self.state.fetch_sub(1, Ordering::Release);
    }

    /// 释放写锁
    fn unlock_write(&self) {
        self.state.fetch_and(!WRITER, Ordering::Release);
    }
}

impl<'a, T> Deref for RwLockReadGuard<'a, T> {
    type Target = T;
    
    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<'a, T> Deref for RwLockWriteGuard<'a, T> {
    type Target = T;
    
    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<'a, T> DerefMut for RwLockWriteGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<'a, T> Drop for RwLockReadGuard<'a, T> {
    fn drop(&mut self) {
        self.lock.unlock_read();
    }
}

impl<'a, T> Drop for RwLockWriteGuard<'a, T> {
    fn drop(&mut self) {
        self.lock.unlock_write();
    }
}

// ============== 顺序锁 (SeqLock) ==============

/// 顺序锁
/// 
/// 用于读者多、写者少且写操作不频繁的场景
pub struct SeqLock<T> {
    sequence: AtomicU32,
    data: UnsafeCell<T>,
}

/// 顺序锁读守卫
pub struct SeqLockReadGuard<'a, T> {
    lock: &'a SeqLock<T>,
    start_seq: u32,
}

unsafe impl<T: Send> Sync for SeqLock<T> {}
unsafe impl<T: Send> Send for SeqLock<T> {}

impl<T: Copy> SeqLock<T> {
    /// 创建新的顺序锁
    pub const fn new(data: T) -> Self {
        Self {
            sequence: AtomicU32::new(0),
            data: UnsafeCell::new(data),
        }
    }

    /// 写操作
    pub fn write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        // 开始写：将序列号变为奇数
        let seq = self.sequence.fetch_add(1, Ordering::Acquire);
        assert!(seq % 2 == 0, "并发写冲突");
        
        fence(Ordering::SeqCst);
        
        // 执行写操作
        let result = f(unsafe { &mut *self.data.get() });
        
        fence(Ordering::SeqCst);
        
        // 结束写：序列号加1变为偶数
        self.sequence.fetch_add(1, Ordering::Release);
        
        result
    }

    /// 读操作（乐观读取，可能重试）
    pub fn read(&self) -> T {
        loop {
            // 等待写完成（序列号为偶数）
            let seq1 = self.sequence.load(Ordering::Acquire);
            if seq1 % 2 != 0 {
                std::hint::spin_loop();
                continue;
            }
            
            fence(Ordering::SeqCst);
            
            // 读取数据
            let data = unsafe { *self.data.get() };
            
            fence(Ordering::SeqCst);
            
            // 检查序列号是否变化
            let seq2 = self.sequence.load(Ordering::Acquire);
            if seq1 == seq2 {
                return data;
            }
            
            // 序列号变化，重试
            std::hint::spin_loop();
        }
    }
}

// ============== 使用示例 ==============

/// 使用标准库 Mutex 的示例
fn demo_std_mutex() {
    println!("\n=== 标准库 Mutex 演示 ===");
    
    let counter = Arc::new(std::sync::Mutex::new(0));
    let mut handles = vec![];
    
    for i in 0..5 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
            println!("线程 {} 增加计数，当前值: {}", i, *num);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("最终计数: {}", *counter.lock().unwrap());
}

/// 使用自定义 SpinLock 的示例
fn demo_spinlock() {
    println!("\n=== 自定义 SpinLock 演示 ===");
    
    let data = Arc::new(SpinLock::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    for i in 0..3 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let mut vec = data.lock();
            vec.push(i + 10);
            println!("线程 {} 添加元素，当前: {:?}", i, *vec);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("最终结果: {:?}", *data.lock());
}

/// 使用自定义 RwLock 的示例
fn demo_rwlock() {
    println!("\n=== 自定义 RwLock 演示 ===");
    
    let data = Arc::new(RwLock::new(String::from("Hello")));
    
    // 多个读者
    let mut read_handles = vec![];
    for i in 0..3 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let s = data.read();
            println!("读者 {} 读取: {}", i, *s);
        });
        read_handles.push(handle);
    }
    
    // 一个写者
    let data_clone = Arc::clone(&data);
    let write_handle = thread::spawn(move || {
        thread::sleep(Duration::from_millis(10)); // 确保读者先读
        let mut s = data_clone.write();
        s.push_str(" World!");
        println!("写者写入: {}", *s);
    });
    
    for handle in read_handles {
        handle.join().unwrap();
    }
    write_handle.join().unwrap();
    
    println!("最终结果: {}", *data.read());
}

/// 使用 SeqLock 的示例
fn demo_seqlock() {
    println!("\n=== 自定义 SeqLock 演示 ===");
    
    let data = Arc::new(SeqLock::new(0u64));
    
    // 写者线程
    let data_write = Arc::clone(&data);
    let write_handle = thread::spawn(move || {
        for i in 1..=5 {
            data_write.write(|v| {
                *v = i * 100;
                println!("写者写入: {}", *v);
            });
            thread::sleep(Duration::from_millis(10));
        }
    });
    
    // 读者线程
    let data_read = Arc::clone(&data);
    let read_handle = thread::spawn(move || {
        for _ in 0..10 {
            let value = data_read.read();
            println!("读者读取: {}", value);
            thread::sleep(Duration::from_millis(8));
        }
    });
    
    write_handle.join().unwrap();
    read_handle.join().unwrap();
}

/// 锁的性能对比
fn benchmark_locks() {
    println!("\n=== 锁性能对比 ===");
    
    const ITERATIONS: usize = 1_000_000;
    
    // 标准库 Mutex
    {
        let lock = Arc::new(std::sync::Mutex::new(0u64));
        let start = std::time::Instant::now();
        
        for _ in 0..ITERATIONS {
            let mut guard = lock.lock().unwrap();
            *guard += 1;
        }
        
        let elapsed = start.elapsed();
        println!("std::sync::Mutex: {:?} ({:?}/op)", 
                 elapsed, elapsed / ITERATIONS as u32);
    }
    
    // 自旋锁（适合短临界区）
    {
        let lock = Arc::new(SpinLock::new(0u64));
        let start = std::time::Instant::now();
        
        for _ in 0..ITERATIONS {
            let mut guard = lock.lock();
            *guard += 1;
        }
        
        let elapsed = start.elapsed();
        println!("SpinLock: {:?} ({:?}/op)", 
                 elapsed, elapsed / ITERATIONS as u32);
    }
    
    // 顺序锁（适合多读少写）
    {
        let lock = Arc::new(SeqLock::new(0u64));
        let start = std::time::Instant::now();
        
        for _ in 0..ITERATIONS {
            lock.write(|v| *v += 1);
        }
        
        let elapsed = start.elapsed();
        println!("SeqLock: {:?} ({:?}/op)", 
                 elapsed, elapsed / ITERATIONS as u32);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spinlock_basic() {
        let lock = SpinLock::new(42);
        assert_eq!(*lock.lock(), 42);
        
        *lock.lock() = 100;
        assert_eq!(*lock.lock(), 100);
    }

    #[test]
    fn test_spinlock_multithreaded() {
        let lock = Arc::new(SpinLock::new(0));
        let mut handles = vec![];
        
        for _ in 0..10 {
            let lock = Arc::clone(&lock);
            handles.push(thread::spawn(move || {
                for _ in 0..100 {
                    let mut guard = lock.lock();
                    *guard += 1;
                }
            }));
        }
        
        for h in handles {
            h.join().unwrap();
        }
        
        assert_eq!(*lock.lock(), 1000);
    }

    #[test]
    fn test_rwlock_read_write() {
        let lock = RwLock::new(10);
        
        // 多个读者
        let r1 = lock.read();
        let r2 = lock.read();
        assert_eq!(*r1, 10);
        assert_eq!(*r2, 10);
        drop(r1);
        drop(r2);
        
        // 写者
        let mut w = lock.write();
        *w = 20;
        drop(w);
        
        assert_eq!(*lock.read(), 20);
    }

    #[test]
    fn test_seqlock_basic() {
        let lock = SeqLock::new(100u64);
        
        assert_eq!(lock.read(), 100);
        
        lock.write(|v| *v = 200);
        assert_eq!(lock.read(), 200);
    }
}

fn main() {
    println!("=== 锁机制演示 ===");
    
    demo_std_mutex();
    demo_spinlock();
    demo_rwlock();
    demo_seqlock();
    benchmark_locks();
    
    println!("\n=== 演示完成 ===");
}
