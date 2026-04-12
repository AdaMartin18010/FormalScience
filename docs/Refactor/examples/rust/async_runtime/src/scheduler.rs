//! # 任务调度器

use std::collections::{BinaryHeap, VecDeque};
use std::future::Future;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use crate::task::{Task, TaskId, TaskState};

/// 调度器 trait
pub trait Scheduler {
    fn push(&mut self, task: Task);
    fn pop(&mut self) -> Option<Task>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn wake(&mut self, id: TaskId);
    fn cleanup(&mut self);
}

/// 先进先出调度器
pub struct FifoScheduler {
    ready: VecDeque<Task>,
    blocked: Vec<Task>,
}

impl FifoScheduler {
    pub fn new() -> Self {
        Self {
            ready: VecDeque::new(),
            blocked: Vec::new(),
        }
    }
}

impl Scheduler for FifoScheduler {
    fn push(&mut self, task: Task) {
        self.ready.push_back(task);
    }
    
    fn pop(&mut self) -> Option<Task> {
        self.ready.pop_front()
    }
    
    fn len(&self) -> usize {
        self.ready.len() + self.blocked.len()
    }
    
    fn is_empty(&self) -> bool {
        self.ready.is_empty() && self.blocked.is_empty()
    }
    
    fn wake(&mut self, id: TaskId) {
        if let Some(pos) = self.blocked.iter().position(|t| t.id() == id) {
            let task = self.blocked.remove(pos);
            self.ready.push_back(task);
        }
    }
    
    fn cleanup(&mut self) {
        self.blocked.retain(|t| t.state() != TaskState::Completed);
    }
}

impl Default for FifoScheduler {
    fn default() -> Self {
        Self::new()
    }
}

/// 优先级任务
pub struct PriorityTask {
    task: Task,
    priority: u32,
}

impl Ord for PriorityTask {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.priority.cmp(&self.priority)
    }
}

impl PartialOrd for PriorityTask {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for PriorityTask {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

impl Eq for PriorityTask {}

/// 优先级调度器
pub struct PriorityScheduler {
    ready: BinaryHeap<PriorityTask>,
    blocked: Vec<PriorityTask>,
}

impl PriorityScheduler {
    pub fn new() -> Self {
        Self {
            ready: BinaryHeap::new(),
            blocked: Vec::new(),
        }
    }
    
    pub fn push_with_priority(&mut self, task: Task, priority: u32) {
        self.ready.push(PriorityTask { task, priority });
    }
}

impl Scheduler for PriorityScheduler {
    fn push(&mut self, task: Task) {
        self.ready.push(PriorityTask { task, priority: 0 });
    }
    
    fn pop(&mut self) -> Option<Task> {
        self.ready.pop().map(|pt| pt.task)
    }
    
    fn len(&self) -> usize {
        self.ready.len() + self.blocked.len()
    }
    
    fn is_empty(&self) -> bool {
        self.ready.is_empty() && self.blocked.is_empty()
    }
    
    fn wake(&mut self, id: TaskId) {
        if let Some(pos) = self.blocked.iter().position(|pt| pt.task.id() == id) {
            let pt = self.blocked.remove(pos);
            self.ready.push(pt);
        }
    }
    
    fn cleanup(&mut self) {
        self.blocked.retain(|pt| pt.task.state() != TaskState::Completed);
    }
}

impl Default for PriorityScheduler {
    fn default() -> Self {
        Self::new()
    }
}

/// 轮转调度器
pub struct RoundRobinScheduler {
    ready: VecDeque<Task>,
    blocked: Vec<Task>,
    time_slice: usize,
    current_ticks: usize,
}

impl RoundRobinScheduler {
    pub fn new(time_slice: usize) -> Self {
        Self {
            ready: VecDeque::new(),
            blocked: Vec::new(),
            time_slice,
            current_ticks: 0,
        }
    }
    
    pub fn tick(&mut self) -> bool {
        self.current_ticks += 1;
        if self.current_ticks >= self.time_slice {
            self.current_ticks = 0;
            true
        } else {
            false
        }
    }
}

impl Scheduler for RoundRobinScheduler {
    fn push(&mut self, task: Task) {
        self.ready.push_back(task);
    }
    
    fn pop(&mut self) -> Option<Task> {
        self.ready.pop_front()
    }
    
    fn len(&self) -> usize {
        self.ready.len() + self.blocked.len()
    }
    
    fn is_empty(&self) -> bool {
        self.ready.is_empty() && self.blocked.is_empty()
    }
    
    fn wake(&mut self, id: TaskId) {
        if let Some(pos) = self.blocked.iter().position(|t| t.id() == id) {
            let task = self.blocked.remove(pos);
            self.ready.push_back(task);
        }
    }
    
    fn cleanup(&mut self) {
        self.blocked.retain(|t| t.state() != TaskState::Completed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    fn dummy_task() -> Task {
        Task::new(async {})
    }
    
    #[test]
    fn test_fifo_scheduler() {
        let mut scheduler = FifoScheduler::new();
        
        let task1 = dummy_task();
        let id1 = task1.id();
        scheduler.push(task1);
        
        let task2 = dummy_task();
        scheduler.push(task2);
        
        assert_eq!(scheduler.len(), 2);
        
        let popped1 = scheduler.pop().unwrap();
        assert_eq!(popped1.id(), id1);
    }
    
    #[test]
    fn test_round_robin_scheduler() {
        let mut scheduler = RoundRobinScheduler::new(10);
        
        scheduler.push(dummy_task());
        scheduler.push(dummy_task());
        
        assert!(!scheduler.tick());
        assert_eq!(scheduler.len(), 2);
    }
}
