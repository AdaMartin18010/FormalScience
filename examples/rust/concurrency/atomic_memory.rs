/// 原子操作和内存序
/// 
/// 演示 Rust 中原子类型的使用、不同内存序的效果和 happens-before 关系

use std::sync::atomic::{
    fence, AtomicBool, AtomicI32, AtomicIsize, AtomicPtr, AtomicU32, AtomicUsize,
    Ordering,
};
use std::sync::Arc;
use std::thread;
use std::time::Instant;

/// 内存序解释和演示
fn memory_ordering_explained() {
    println!("=== 内存序详解 ===\n");

    println!("1. Relaxed - 最弱约束，只保证原子性:");
    println!("   - 没有同步或排序约束");
    println!("   - 仅保证操作是原子的，不会数据竞争");
    println!("   - 使用场景：简单的计数器\n");

    println!("2. Acquire - 获取语义:");
    println!("   - 用于读取操作");
    println!("   - 保证此后的读操作不会被重排序到此操作之前");
    println!("   - 与 Release 配对使用\n");

    println!("3. Release - 释放语义:");
    println!("   - 用于写入操作");
    println!("   - 保证此前的读写操作不会被重排序到此操作之后");
    println!("   - 与 Acquire 配对使用\n");

    println!("4. AcqRel - 获取-释放语义:");
    println!("   - 用于读写操作（如 fetch_add）");
    println!("   - 兼具 Acquire 和 Release 的语义\n");

    println!("5. SeqCst - 顺序一致性:");
    println!("   - 最强约束");
    println!("   - 所有线程以相同顺序看到操作");
    println!("   - 性能开销最大\n");
}

/// 使用不同内存序的原子计数器
fn atomic_counter_demo() {
    println!("\n=== 原子计数器演示 ===");

    // Relaxed - 简单计数
    let counter = AtomicUsize::new(0);
    for _ in 0..1000 {
        counter.fetch_add(1, Ordering::Relaxed);
    }
    println!("Relaxed 计数结果: {}", counter.load(Ordering::Relaxed));

    // SeqCst - 保证顺序一致性
    let counter2 = AtomicUsize::new(0);
    let c1 = Arc::new(counter2);
    let c2 = Arc::clone(&c1);
    let c3 = Arc::clone(&c1);

    let t1 = thread::spawn(move || {
        for _ in 0..500 {
            c1.fetch_add(1, Ordering::SeqCst);
        }
    });

    let t2 = thread::spawn(move || {
        for _ in 0..500 {
            c2.fetch_add(1, Ordering::SeqCst);
        }
    });

    t1.join().unwrap();
    t2.join().unwrap();

    println!("SeqCst 并发计数结果: {}", c3.load(Ordering::SeqCst));
}

/// Acquire-Release 语义演示
fn acquire_release_demo() {
    println!("\n=== Acquire-Release 语义演示 ===");

    let data = Arc::new(AtomicUsize::new(0));
    let ready = Arc::new(AtomicBool::new(false));

    let data_clone = Arc::clone(&data);
    let ready_clone = Arc::clone(&ready);

    // 生产者线程
    let producer = thread::spawn(move || {
        // 先写入数据
        data_clone.store(42, Ordering::Relaxed);
        
        // Release: 确保上面的写入对此操作可见
        ready_clone.store(true, Ordering::Release);
        println!("生产者: 数据已准备");
    });

    // 消费者线程
    let consumer = thread::spawn(move || {
        // Acquire: 确保能看到 Release 之前的所有写入
        while !ready.load(Ordering::Acquire) {
            thread::yield_now();
        }
        
        // 现在读取数据是安全的
        let value = data.load(Ordering::Relaxed);
        println!("消费者: 读取到数据 {}", value);
        assert_eq!(value, 42);
    });

    producer.join().unwrap();
    consumer.join().unwrap();
}

/// 内存屏障 (Fence) 演示
fn fence_demo() {
    println!("\n=== 内存屏障演示 ===");

    let x = Arc::new(AtomicUsize::new(0));
    let y = Arc::new(AtomicUsize::new(0));

    let x2 = Arc::clone(&x);
    let y2 = Arc::clone(&y);

    let t1 = thread::spawn(move || {
        x2.store(1, Ordering::Relaxed);
        
        // 内存屏障：确保 x=1 在 y=1 之前对其他线程可见
        fence(Ordering::Release);
        
        y2.store(1, Ordering::Relaxed);
    });

    let t2 = thread::spawn(move || {
        while y.load(Ordering::Relaxed) == 0 {}
        
        // 内存屏障：确保看到 y=1 后，也能看到 x=1
        fence(Ordering::Acquire);
        
        let x_val = x.load(Ordering::Relaxed);
        println!("线程2: 看到 y=1, x={}", x_val);
        
        // 如果没有 fence，可能看到 x=0
        assert!(x_val == 1, "x 应该是 1");
    });

    t1.join().unwrap();
    t2.join().unwrap();
    println!("内存屏障确保了正确的 happens-before 关系");
}

/// 原子指针操作
fn atomic_pointer_demo() {
    println!("\n=== 原子指针操作 ===");

    let data = vec![1, 2, 3, 4, 5];
    let ptr = AtomicPtr::new(data.as_ptr() as *mut i32);

    // 加载指针
    let loaded = ptr.load(Ordering::Acquire);
    println!("加载的指针: {:?}", loaded);
    
    unsafe {
        println!("指针指向的值: {}", *loaded);
    }

    // 比较交换指针
    let new_data = vec![10, 20, 30];
    let new_ptr = new_data.as_ptr() as *mut i32;

    match ptr.compare_exchange(
        loaded,
        new_ptr,
        Ordering::AcqRel,
        Ordering::Acquire,
    ) {
        Ok(_) => println!("指针交换成功"),
        Err(actual) => println!("指针交换失败，实际值: {:?}", actual),
    }
}

/// 自旋锁使用内存序的示例
struct AtomicSpinLock<T> {
    locked: AtomicBool,
    data: std::cell::UnsafeCell<T>,
}

unsafe impl<T: Send> Send for AtomicSpinLock<T> {}
unsafe impl<T: Send> Sync for AtomicSpinLock<T> {}

impl<T> AtomicSpinLock<T> {
    fn new(data: T) -> Self {
        Self {
            locked: AtomicBool::new(false),
            data: std::cell::UnsafeCell::new(data),
        }
    }

    fn lock(&self) -> AtomicSpinLockGuard<T> {
        // 自旋等待获取锁
        while self
            .locked
            .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            std::hint::spin_loop();
        }
        
        AtomicSpinLockGuard { lock: self }
    }
}

struct AtomicSpinLockGuard<'a, T> {
    lock: &'a AtomicSpinLock<T>,
}

impl<'a, T> std::ops::Deref for AtomicSpinLockGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<'a, T> std::ops::DerefMut for AtomicSpinLockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<'a, T> Drop for AtomicSpinLockGuard<'a, T> {
    fn drop(&mut self) {
        // Release: 确保所有之前的写入在解锁后可见
        self.lock.locked.store(false, Ordering::Release);
    }
}

fn spinlock_demo() {
    println!("\n=== 原子自旋锁演示 ===");

    let lock = Arc::new(AtomicSpinLock::new(0));
    let mut handles = vec![];

    for i in 0..5 {
        let lock = Arc::clone(&lock);
        handles.push(thread::spawn(move || {
            let mut guard = lock.lock();
            *guard += 1;
            println!("线程 {} 增加计数到 {}", i, *guard);
        }));
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("最终值: {}", *lock.lock());
}

/// 比较不同内存序的性能
fn benchmark_memory_orderings() {
    println!("\n=== 内存序性能对比 ===");

    const ITERATIONS: usize = 10_000_000;

    // Relaxed
    {
        let counter = AtomicUsize::new(0);
        let start = Instant::now();
        
        for _ in 0..ITERATIONS {
            counter.fetch_add(1, Ordering::Relaxed);
        }
        
        let elapsed = start.elapsed();
        println!(
            "Relaxed: {:?} ({:?}/iter)",
            elapsed,
            elapsed / ITERATIONS as u32
        );
    }

    // SeqCst
    {
        let counter = AtomicUsize::new(0);
        let start = Instant::now();
        
        for _ in 0..ITERATIONS {
            counter.fetch_add(1, Ordering::SeqCst);
        }
        
        let elapsed = start.elapsed();
        println!(
            "SeqCst:  {:?} ({:?}/iter)",
            elapsed,
            elapsed / ITERATIONS as u32
        );
    }

    // 并发场景下的对比
    println!("\n并发场景 (4线程，各执行 {} 次):", ITERATIONS / 4);

    // Relaxed 并发
    {
        let counter = Arc::new(AtomicUsize::new(0));
        let start = Instant::now();
        
        let mut handles = vec![];
        for _ in 0..4 {
            let c = Arc::clone(&counter);
            handles.push(thread::spawn(move || {
                for _ in 0..ITERATIONS / 4 {
                    c.fetch_add(1, Ordering::Relaxed);
                }
            }));
        }
        
        for h in handles {
            h.join().unwrap();
        }
        
        let elapsed = start.elapsed();
        println!("Relaxed (4线程): {:?}", elapsed);
    }

    // SeqCst 并发
    {
        let counter = Arc::new(AtomicUsize::new(0));
        let start = Instant::now();
        
        let mut handles = vec![];
        for _ in 0..4 {
            let c = Arc::clone(&counter);
            handles.push(thread::spawn(move || {
                for _ in 0..ITERATIONS / 4 {
                    c.fetch_add(1, Ordering::SeqCst);
                }
            }));
        }
        
        for h in handles {
            h.join().unwrap();
        }
        
        let elapsed = start.elapsed();
        println!("SeqCst (4线程):  {:?}", elapsed);
        println!("计数结果: {}", counter.load(Ordering::SeqCst));
    }
}

/// 各种原子操作演示
fn atomic_operations_demo() {
    println!("\n=== 原子操作演示 ===");

    // fetch_add / fetch_sub
    let counter = AtomicI32::new(10);
    let prev = counter.fetch_add(5, Ordering::SeqCst);
    println!("fetch_add: 前值={}, 当前值={}", prev, counter.load(Ordering::SeqCst));

    // fetch_and / fetch_or / fetch_xor
    let flags = AtomicU32::new(0b1010);
    let prev = flags.fetch_or(0b0100, Ordering::SeqCst);
    println!("fetch_or:  前值={:04b}, 当前值={:04b}", prev, flags.load(Ordering::SeqCst));

    // compare_exchange
    let value = AtomicU32::new(100);
    match value.compare_exchange(100, 200, Ordering::SeqCst, Ordering::SeqCst) {
        Ok(_) => println!("compare_exchange: 100 -> 200 成功"),
        Err(actual) => println!("compare_exchange: 失败，实际值={}", actual),
    }

    // fetch_max / fetch_min (Rust 1.45+)
    let max_val = AtomicU32::new(50);
    max_val.fetch_max(100, Ordering::SeqCst);
    println!("fetch_max(100): {}", max_val.load(Ordering::SeqCst));
    max_val.fetch_max(30, Ordering::SeqCst);
    println!("fetch_max(30):  {}", max_val.load(Ordering::SeqCst));

    // swap
    let data = AtomicU32::new(42);
    let old = data.swap(100, Ordering::SeqCst);
    println!("swap: 旧值={}, 新值={}", old, data.load(Ordering::SeqCst));
}

/// 无锁标志位操作
fn bit_manipulation_demo() {
    println!("\n=== 原子位操作演示 ===");

    // 使用单个原子变量存储多个标志位
    const FLAG_A: u32 = 1 << 0;
    const FLAG_B: u32 = 1 << 1;
    const FLAG_C: u32 = 1 << 2;

    let flags = AtomicU32::new(0);

    // 设置标志位
    flags.fetch_or(FLAG_A | FLAG_B, Ordering::SeqCst);
    println!("设置 A, B: {:04b}", flags.load(Ordering::SeqCst));

    // 检查标志位
    let current = flags.load(Ordering::SeqCst);
    println!("FLAG_A 设置: {}", current & FLAG_A != 0);
    println!("FLAG_C 设置: {}", current & FLAG_C != 0);

    // 清除标志位
    flags.fetch_and(!FLAG_B, Ordering::SeqCst);
    println!("清除 B:    {:04b}", flags.load(Ordering::SeqCst));

    // 切换标志位
    flags.fetch_xor(FLAG_A | FLAG_C, Ordering::SeqCst);
    println!("切换 A, C: {:04b}", flags.load(Ordering::SeqCst));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atomic_counter() {
        let counter = AtomicUsize::new(0);
        
        counter.fetch_add(10, Ordering::SeqCst);
        assert_eq!(counter.load(Ordering::SeqCst), 10);
        
        counter.fetch_sub(5, Ordering::SeqCst);
        assert_eq!(counter.load(Ordering::SeqCst), 5);
    }

    #[test]
    fn test_compare_exchange() {
        let value = AtomicU32::new(100);
        
        // 成功的情况
        assert!(value.compare_exchange(100, 200, Ordering::SeqCst, Ordering::SeqCst).is_ok());
        assert_eq!(value.load(Ordering::SeqCst), 200);
        
        // 失败的情况
        assert!(value.compare_exchange(100, 300, Ordering::SeqCst, Ordering::SeqCst).is_err());
        assert_eq!(value.load(Ordering::SeqCst), 200);
    }

    #[test]
    fn test_acquire_release() {
        let data = Arc::new(AtomicUsize::new(0));
        let ready = Arc::new(AtomicBool::new(false));

        let data_clone = Arc::clone(&data);
        let ready_clone = Arc::clone(&ready);

        thread::spawn(move || {
            data_clone.store(42, Ordering::Relaxed);
            ready_clone.store(true, Ordering::Release);
        }).join().unwrap();

        while !ready.load(Ordering::Acquire) {
            thread::yield_now();
        }

        assert_eq!(data.load(Ordering::Relaxed), 42);
    }

    #[test]
    fn test_atomic_spinlock() {
        let lock = Arc::new(AtomicSpinLock::new(0));
        let mut handles = vec![];

        for _ in 0..10 {
            let lock = Arc::clone(&lock);
            handles.push(thread::spawn(move || {
                let mut guard = lock.lock();
                *guard += 1;
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(*lock.lock(), 10);
    }
}

fn main() {
    println!("=== 原子操作和内存序演示 ===");

    memory_ordering_explained();
    atomic_counter_demo();
    acquire_release_demo();
    fence_demo();
    atomic_pointer_demo();
    spinlock_demo();
    atomic_operations_demo();
    bit_manipulation_demo();
    benchmark_memory_orderings();

    println!("\n=== 演示完成 ===");
}
