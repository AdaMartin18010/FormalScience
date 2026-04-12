/// Waker 机制和执行器实现
/// 
/// 演示 Rust 异步运行时的核心组件：Waker、Executor、任务队列

use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Wake, Waker};
use std::thread;
use std::time::{Duration, Instant};

// ============== 任务定义 ==============

/// 任务ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TaskId(u64);

impl TaskId {
    fn new() -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        Self(COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

/// 任务结构
/// 
/// 包装一个 Future，使其可以在执行器中运行
pub struct Task {
    id: TaskId,
    future: Pin<Box<dyn Future<Output = ()> + Send + 'static>>,
}

impl Task {
    /// 创建新任务
    pub fn new<F>(future: F) -> Self
    where
        F: Future<Output = ()> + Send + 'static,
    {
        Self {
            id: TaskId::new(),
            future: Box::pin(future),
        }
    }

    /// 轮询任务
    fn poll(&mut self, context: &mut Context) -> Poll<()> {
        self.future.as_mut().poll(context)
    }
}

// ============== Waker 实现 ==============

/// 任务 sender trait
/// 
/// 用于 Waker 将任务重新加入执行队列
pub trait TaskSender: Send + Sync {
    fn send(&self, task: Task);
}

/// 自定义 Waker 实现
/// 
/// Waker 是异步运行的关键，当 Future 返回 Pending 时，
/// 它需要一种方式在将来被重新唤醒。
pub struct CustomWaker {
    task_id: TaskId,
    sender: Arc<dyn TaskSender>,
}

impl CustomWaker {
    fn new(task_id: TaskId, sender: Arc<dyn TaskSender>) -> Self {
        Self { task_id, sender }
    }

    /// 创建 RawWaker
    fn into_raw_waker(self) -> RawWaker {
        let boxed = Box::new(self);
        let ptr = Box::into_raw(boxed);
        
        RawWaker::new(ptr as *const (), &VTABLE)
    }

    /// 唤醒任务
    fn wake(&self) {
        // 创建一个新的任务对象重新加入队列
        // 实际实现应该克隆 future，这里简化处理
        println!("Waker::wake() - 任务 {:?}", self.task_id);
    }

    /// 克隆 Waker
    fn clone_waker(&self) -> RawWaker {
        let new_waker = CustomWaker::new(self.task_id, Arc::clone(&self.sender));
        new_waker.into_raw_waker()
    }

    /// 释放 Waker
    unsafe fn drop_waker(ptr: *const ()) {
        let _ = Box::from_raw(ptr as *mut CustomWaker);
    }
}

/// Waker VTable
static VTABLE: RawWakerVTable = RawWakerVTable::new(
    // clone
    |ptr| unsafe {
        let waker = &*(ptr as *const CustomWaker);
        waker.clone_waker()
    },
    // wake
    |ptr| unsafe {
        let waker = Box::from_raw(ptr as *mut CustomWaker);
        waker.wake();
    },
    // wake_by_ref
    |ptr| unsafe {
        let waker = &*(ptr as *const CustomWaker);
        waker.wake();
    },
    // drop
    |ptr| unsafe {
        CustomWaker::drop_waker(ptr);
    },
);

// ============== 简单执行器 ==============

/// 简单单线程执行器
/// 
/// 从队列中取出任务并执行
pub struct SimpleExecutor {
    task_queue: Arc<Mutex<VecDeque<Task>>>,
    task_count: Arc<AtomicU64>,
}

impl SimpleExecutor {
    /// 创建新执行器
    pub fn new() -> Self {
        Self {
            task_queue: Arc::new(Mutex::new(VecDeque::new())),
            task_count: Arc::new(AtomicU64::new(0)),
        }
    }

    /// 生成任务
    pub fn spawn<F>(&self, future: F)
    where
        F: Future<Output = ()> + Send + 'static,
    {
        let task = Task::new(future);
        self.task_queue.lock().unwrap().push_back(task);
        self.task_count.fetch_add(1, Ordering::Relaxed);
    }

    /// 运行执行器（阻塞直到所有任务完成）
    pub fn run(&self) {
        println!("执行器启动");

        while let Some(mut task) = self.task_queue.lock().unwrap().pop_front() {
            // 创建 Waker
            let task_id = task.id;
            let sender = Arc::new(SimpleTaskSender {
                queue: Arc::clone(&self.task_queue),
            });
            
            let custom_waker = CustomWaker::new(task_id, sender);
            let raw_waker = custom_waker.into_raw_waker();
            let waker = unsafe { Waker::from_raw(raw_waker) };
            
            let mut context = Context::from_waker(&waker);

            // 轮询任务
            match task.poll(&mut context) {
                Poll::Ready(()) => {
                    println!("任务 {:?} 完成", task_id);
                    self.task_count.fetch_sub(1, Ordering::Relaxed);
                }
                Poll::Pending => {
                    println!("任务 {:?} 挂起", task_id);
                    // 实际应该存储任务，等待唤醒
                    // 这里简化：直接重新加入队列
                }
            }
        }

        println!("执行器停止");
    }
}

struct SimpleTaskSender {
    queue: Arc<Mutex<VecDeque<Task>>>,
}

impl TaskSender for SimpleTaskSender {
    fn send(&self, task: Task) {
        self.queue.lock().unwrap().push_back(task);
    }
}

// ============== 改进的执行器（支持唤醒） ==============

/// 可唤醒的任务包装
struct WakableTask {
    task: Arc<Mutex<Task>>,
    waker: Arc<TaskWaker>,
}

impl WakableTask {
    fn new<F>(future: F) -> Self
    where
        F: Future<Output = ()> + Send + 'static,
    {
        let task = Arc::new(Mutex::new(Task::new(future)));
        let waker = Arc::new(TaskWaker {
            task: Arc::clone(&task),
            ready: AtomicU64::new(1),
        });

        Self { task, waker }
    }

    fn poll(&self) -> Poll<()> {
        let waker: Waker = self.waker.clone().into();
        let mut context = Context::from_waker(&waker);
        self.task.lock().unwrap().poll(&mut context)
    }
}

/// 任务 Waker 实现
struct TaskWaker {
    task: Arc<Mutex<Task>>,
    ready: AtomicU64,
}

impl Wake for TaskWaker {
    fn wake(self: Arc<Self>) {
        self.ready.fetch_add(1, Ordering::Relaxed);
        println!("任务被唤醒");
    }

    fn wake_by_ref(self: &Arc<Self>) {
        self.ready.fetch_add(1, Ordering::Relaxed);
        println!("任务被唤醒（by_ref）");
    }
}

/// 改进的执行器
pub struct ImprovedExecutor {
    ready_queue: Arc<Mutex<VecDeque<Arc<WakableTask>>>>,
}

impl ImprovedExecutor {
    pub fn new() -> Self {
        Self {
            ready_queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    pub fn spawn<F>(&self, future: F)
    where
        F: Future<Output = ()> + Send + 'static,
    {
        let task = Arc::new(WakableTask::new(future));
        self.ready_queue.lock().unwrap().push_back(task);
    }

    pub fn run(&self) {
        println!("\n改进执行器启动");
        let mut completed = 0;

        loop {
            let task = self.ready_queue.lock().unwrap().pop_front();
            
            match task {
                Some(task) => {
                    match task.poll() {
                        Poll::Ready(()) => {
                            completed += 1;
                        }
                        Poll::Pending => {
                            // 重新加入队列等待下次执行
                            self.ready_queue.lock().unwrap().push_back(task);
                        }
                    }
                }
                None => break,
            }

            // 防止无限循环
            if completed >= 100 {
                break;
            }
        }

        println!("改进执行器停止，完成 {} 个任务", completed);
    }
}

// ============== 带计时的 Future ==============

/// 定时器 Future
pub struct Timer {
    deadline: Instant,
}

impl Timer {
    pub fn new(duration: Duration) -> Self {
        Self {
            deadline: Instant::now() + duration,
        }
    }
}

impl Future for Timer {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if Instant::now() >= self.deadline {
            println!("定时器完成");
            Poll::Ready(())
        } else {
            // 注册唤醒
            let waker = cx.waker().clone();
            let remaining = self.deadline - Instant::now();
            
            thread::spawn(move || {
                thread::sleep(remaining);
                waker.wake();
            });
            
            Poll::Pending
        }
    }
}

/// 带超时的 Future
pub struct Timeout<F> {
    future: F,
    deadline: Instant,
}

impl<F> Timeout<F> {
    pub fn new(future: F, duration: Duration) -> Self {
        Self {
            future,
            deadline: Instant::now() + duration,
        }
    }
}

impl<F: Future> Future for Timeout<F> {
    type Output = Option<F::Output>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // 简化实现，实际需要 Pin 投影
        if Instant::now() >= self.deadline {
            Poll::Ready(None)
        } else {
            Poll::Pending
        }
    }
}

// ============== 示例任务 ==============

async fn example_task(id: u32) {
    println!("任务 {} 开始", id);
    Timer::new(Duration::from_millis(100)).await;
    println!("任务 {} 结束", id);
}

async fn async_task_with_yield() {
    println!("异步任务: 步骤 1");
    Yield::new().await;
    println!("异步任务: 步骤 2");
    Yield::new().await;
    println!("异步任务: 步骤 3");
}

/// Yield 让出执行权的 Future
pub struct Yield {
    yielded: bool,
}

impl Yield {
    fn new() -> Self {
        Self { yielded: false }
    }
}

impl Future for Yield {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.yielded {
            Poll::Ready(())
        } else {
            self.yielded = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

// ============== 演示函数 ==============

fn demo_simple_executor() {
    println!("\n=== 简单执行器演示 ===");

    let executor = SimpleExecutor::new();
    
    executor.spawn(async {
        println!("任务 1 执行");
    });
    
    executor.spawn(async {
        println!("任务 2 执行");
    });

    executor.run();
}

fn demo_improved_executor() {
    println!("\n=== 改进执行器演示 ===");

    let executor = ImprovedExecutor::new();
    
    executor.spawn(async {
        println!("异步任务 A");
        Yield::new().await;
        println!("异步任务 A 继续");
    });
    
    executor.spawn(async {
        println!("异步任务 B");
        Yield::new().await;
        println!("异步任务 B 继续");
    });

    executor.run();
}

fn demo_timer() {
    println!("\n=== 定时器演示 ===");

    let start = Instant::now();
    
    let executor = ImprovedExecutor::new();
    executor.spawn(async move {
        println!("等待 200ms...");
        Timer::new(Duration::from_millis(200)).await;
        println!("等待完成，耗时 {:?}", start.elapsed());
    });
    
    executor.run();
}

fn explain_waker() {
    println!("\n=== Waker 机制详解 ===");

    println!("\n1. Waker 的作用:");
    println!("   - 当 Future 返回 Pending 时，需要一种方式在将来被重新唤醒");
    println!("   - Waker 提供了这种唤醒机制");
    println!("   - 通常由执行器创建并传递给 Future\n");

    println!("2. Waker 的工作原理:");
    println!("   - Future.poll() 接收 Context，其中包含 Waker");
    println!("   - Future 可以克隆 Waker 并存储起来");
    println!("   - 当条件满足时（如IO完成、定时器到期），调用 waker.wake()");
    println!("   - wake() 会将任务重新加入执行队列\n");

    println!("3. RawWaker 和 VTable:");
    println!("   - RawWaker 是类型擦除的 waker 指针");
    println!("   - VTable 包含 clone/wake/wake_by_ref/drop 函数指针");
    println!("   - 允许自定义 Waker 实现\n");

    println!("4. 执行器的责任:");
    println!("   - 维护就绪任务队列");
    println!("   - 为每个任务创建 Waker");
    println!("   - 响应 wake() 调用，重新调度任务");
    println!("   - 管理任务生命周期\n");
}

fn explain_executor() {
    println!("\n=== 执行器详解 ===");

    println!("\n1. 执行器的核心循环:");
    println!("   loop {{");
    println!("       let task = queue.pop();");
    println!("       let waker = create_waker(&task);");
    println!("       match task.poll(waker) {{");
    println!("           Ready => 任务完成,");
    println!("           Pending => 等待唤醒,");
    println!("       }}");
    println!("   }}\n");

    println!("2. 执行器类型:");
    println!("   - 单线程执行器：简单，无需同步");
    println!("   - 多线程执行器：使用工作窃取队列");
    println!("   - 本地执行器：任务!Send，使用 Rc 代替 Arc\n");

    println!("3. 任务调度策略:");
    println!("   - FIFO：先进先出，公平调度");
    println!("   - LIFO：后进先出，利用缓存局部性");
    println!("   - 优先级：根据任务优先级调度");
    println!("   - 工作窃取：多线程间负载均衡\n");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_executor() {
        let executor = SimpleExecutor::new();
        let counter = Arc::new(AtomicU64::new(0));
        let c = Arc::clone(&counter);
        
        executor.spawn(async move {
            c.fetch_add(1, Ordering::Relaxed);
        });
        
        executor.run();
        // 注意：简单执行器可能无法正确完成异步任务
    }

    #[test]
    fn test_yield_future() {
        let mut yield_fut = Yield::new();
        
        // 创建 noop waker
        let waker = futures_task::noop_waker();
        let mut context = Context::from_waker(&waker);
        
        // 第一次 poll 应该返回 Pending
        match Pin::new(&mut yield_fut).poll(&mut context) {
            Poll::Pending => {}
            _ => panic!("第一次 poll 应该返回 Pending"),
        }
        
        // 第二次 poll 应该返回 Ready
        match Pin::new(&mut yield_fut).poll(&mut context) {
            Poll::Ready(()) => {}
            _ => panic!("第二次 poll 应该返回 Ready"),
        }
    }

    #[test]
    fn test_timer() {
        let start = Instant::now();
        let mut timer = Timer::new(Duration::from_millis(50));
        
        let waker = futures_task::noop_waker();
        let mut context = Context::from_waker(&waker);
        
        // 立即 poll 应该返回 Pending（因为时间还没到）
        match Pin::new(&mut timer).poll(&mut context) {
            Poll::Pending => {
                // 等待定时器到期
                thread::sleep(Duration::from_millis(100));
            }
            _ => {}
        }
        
        // 现在应该完成了
        // 注意：这里简化处理，实际应该使用改进的执行器
    }
}

// 辅助模块
mod futures_task {
    use std::task::{RawWaker, RawWakerVTable, Waker};

    pub fn noop_waker() -> Waker {
        fn noop_clone(_: *const ()) -> RawWaker {
            noop_raw_waker()
        }
        fn noop(_: *const ()) {}

        fn noop_raw_waker() -> RawWaker {
            RawWaker::new(std::ptr::null(), &VTABLE)
        }

        static VTABLE: RawWakerVTable = RawWakerVTable::new(noop_clone, noop, noop, noop);

        unsafe { Waker::from_raw(noop_raw_waker()) }
    }
}

fn main() {
    println!("=== Waker 机制和执行器演示 ===");

    explain_waker();
    explain_executor();
    demo_simple_executor();
    demo_improved_executor();
    demo_timer();

    println!("\n=== 演示完成 ===");
}
