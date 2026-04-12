//! # Reactor 模式实现
//! 
//! 事件驱动的 I/O 多路复用

use std::collections::HashMap;
use std::io;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::task::Waker;
use std::time::{Duration, Instant};

/// 事件类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    Readable,
    Writable,
    Error,
    Timeout,
}

/// 事件 ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EventId(u64);

impl EventId {
    pub fn new() -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        EventId(COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

impl Default for EventId {
    fn default() -> Self {
        Self::new()
    }
}

/// I/O 资源句柄
pub struct IoHandle {
    id: EventId,
}

impl IoHandle {
    pub fn id(&self) -> EventId {
        self.id
    }
}

/// Reactor：事件循环核心
pub struct Reactor {
    timers: Arc<Mutex<Vec<TimerEntry>>>,
}

struct TimerEntry {
    deadline: Instant,
    waker: Waker,
    id: EventId,
}

impl Reactor {
    pub fn new() -> Self {
        Self {
            timers: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    /// 注册定时器
    pub fn register_timer(&self, delay: Duration, waker: Waker) -> EventId {
        let id = EventId::new();
        let deadline = Instant::now() + delay;
        
        let timer = TimerEntry {
            deadline,
            waker,
            id,
        };
        
        self.timers.lock().unwrap().push(timer);
        
        id
    }
    
    /// 注销事件
    pub fn unregister(&self, id: EventId) {
        let mut timers = self.timers.lock().unwrap();
        timers.retain(|t| t.id != id);
    }
    
    /// 运行一次事件循环
    pub fn poll(&self, timeout: Option<Duration>) -> io::Result<()> {
        let deadline = timeout.map(|d| Instant::now() + d);
        
        loop {
            if let Some(d) = deadline {
                if Instant::now() >= d {
                    break;
                }
            }
            
            self.process_timers();
            
            std::thread::sleep(Duration::from_millis(1));
        }
        
        Ok(())
    }
    
    fn process_timers(&self) {
        let now = Instant::now();
        let mut timers = self.timers.lock().unwrap();
        
        let expired: Vec<usize> = timers
            .iter()
            .enumerate()
            .filter(|(_, t)| t.deadline <= now)
            .map(|(i, _)| i)
            .collect();
        
        for i in expired.into_iter().rev() {
            let timer = timers.remove(i);
            timer.waker.wake();
        }
    }
}

impl Default for Reactor {
    fn default() -> Self {
        Self::new()
    }
}

/// 事件通知器
pub struct EventNotifier {
    wakers: Arc<Mutex<Vec<Waker>>>,
}

impl EventNotifier {
    pub fn new() -> Self {
        Self {
            wakers: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    pub fn subscribe(&self, waker: Waker) {
        self.wakers.lock().unwrap().push(waker);
    }
    
    pub fn notify_all(&self) {
        let wakers = std::mem::take(&mut *self.wakers.lock().unwrap());
        for waker in wakers {
            waker.wake();
        }
    }
    
    pub fn notify_one(&self) {
        if let Some(waker) = self.wakers.lock().unwrap().pop() {
            waker.wake();
        }
    }
}

impl Default for EventNotifier {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_reactor_register() {
        let reactor = Reactor::new();
        
        let waker = Arc::new(std::task::Wake::noop()).into();
        let id = reactor.register_timer(Duration::from_secs(1), waker);
        
        assert_ne!(id, EventId::default());
    }
}
