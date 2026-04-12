//! # 任务管理

use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::task::{Context, Poll, Wake};

/// 任务 ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TaskId(u64);

impl TaskId {
    pub fn new() -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        TaskId(COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

impl Default for TaskId {
    fn default() -> Self {
        Self::new()
    }
}

/// 任务状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskState {
    Ready,
    Running,
    Blocked,
    Completed,
}

/// 任务结构
pub struct Task {
    id: TaskId,
    state: TaskState,
    future: Pin<Box<dyn Future<Output = ()> + Send>>,
}

impl Task {
    pub fn new<F>(future: F) -> Self
    where
        F: Future<Output = ()> + Send + 'static,
    {
        Self {
            id: TaskId::new(),
            state: TaskState::Ready,
            future: Box::pin(future),
        }
    }
    
    pub fn id(&self) -> TaskId {
        self.id
    }
    
    pub fn state(&self) -> TaskState {
        self.state
    }
    
    pub fn poll(&mut self, context: &mut Context) -> Poll<()> {
        self.state = TaskState::Running;
        match self.future.as_mut().poll(context) {
            Poll::Ready(()) => {
                self.state = TaskState::Completed;
                Poll::Ready(())
            }
            Poll::Pending => {
                self.state = TaskState::Blocked;
                Poll::Pending
            }
        }
    }
}

/// 任务队列
pub struct TaskQueue {
    tasks: Vec<Task>,
}

impl TaskQueue {
    pub fn new() -> Self {
        Self { tasks: Vec::new() }
    }
    
    pub fn push(&mut self, task: Task) {
        self.tasks.push(task);
    }
    
    pub fn pop(&mut self) -> Option<Task> {
        let index = self.tasks.iter().position(|t| t.state() == TaskState::Ready)?;
        Some(self.tasks.remove(index))
    }
    
    pub fn len(&self) -> usize {
        self.tasks.len()
    }
    
    pub fn is_empty(&self) -> bool {
        self.tasks.is_empty()
    }
    
    pub fn cleanup_completed(&mut self) {
        self.tasks.retain(|t| t.state() != TaskState::Completed);
    }
    
    /// 标记任务为就绪
    pub fn mark_ready(&mut self, id: TaskId) {
        if let Some(task) = self.tasks.iter_mut().find(|t| t.id() == id) {
            if task.state == TaskState::Blocked {
                task.state = TaskState::Ready;
            }
        }
    }
}

impl Default for TaskQueue {
    fn default() -> Self {
        Self::new()
    }
}

/// 任务唤醒器
pub struct TaskWaker {
    task_id: TaskId,
}

impl TaskWaker {
    pub fn new(task_id: TaskId) -> Arc<Self> {
        Arc::new(Self { task_id })
    }
    
    pub fn task_id(&self) -> TaskId {
        self.task_id
    }
}

impl Wake for TaskWaker {
    fn wake(self: Arc<Self>) {
        println!("Task {:?} woken", self.task_id);
    }
    
    fn wake_by_ref(self: &Arc<Self>) {
        println!("Task {:?} woken by ref", self.task_id);
    }
}

/// 产生执行权
pub struct YieldNow;

impl std::future::Future for YieldNow {
    type Output = ();
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        cx.waker().wake_by_ref();
        Poll::Pending
    }
}

pub async fn yield_now() {
    YieldNow.await;
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_task_id() {
        let id1 = TaskId::new();
        let id2 = TaskId::new();
        assert_ne!(id1, id2);
    }
    
    #[test]
    fn test_task_queue() {
        let mut queue = TaskQueue::new();
        
        let task = Task::new(async move {
            println!("Task executing");
        });
        
        queue.push(task);
        assert_eq!(queue.len(), 1);
    }
}
