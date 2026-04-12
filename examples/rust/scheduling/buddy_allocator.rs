/// 伙伴系统内存分配器实现
/// 
/// 伙伴系统是一种经典的内存分配算法，将内存划分为大小为2的幂的块。
/// 分配时找到最小的足够大的块，释放时与相邻的"伙伴"块合并。

use std::collections::LinkedList;
use std::ptr::NonNull;

/// 内存块大小常量
pub const MIN_BLOCK_SIZE: usize = 16;  // 最小块大小（字节）
pub const MAX_BLOCK_SIZE: usize = 4096; // 最大块大小（字节）
pub const POOL_SIZE: usize = 16384;     // 内存池总大小（字节）

/// 空闲内存块
#[derive(Debug)]
struct FreeBlock {
    /// 块大小
    size: usize,
    /// 下一个空闲块
    next: Option<NonNull<FreeBlock>>,
}

impl FreeBlock {
    fn new(size: usize) -> Self {
        Self { size, next: None }
    }
}

/// 伙伴系统分配器
pub struct BuddyAllocator {
    /// 内存池
    pool: Vec<u8>,
    /// 各级空闲链表（按大小索引）
    /// 索引 0 -> 16 bytes, 1 -> 32 bytes, ...
    free_lists: Vec<LinkedList<usize>>, // 存储偏移量
    /// 当前内存池使用统计
    used_bytes: usize,
    /// 分配次数统计
    alloc_count: usize,
    /// 释放次数统计
    free_count: usize,
}

impl BuddyAllocator {
    /// 创建新的伙伴系统分配器
    pub fn new() -> Self {
        let pool = vec![0u8; POOL_SIZE];
        
        // 计算需要的层级数
        let num_levels = Self::size_to_level(MAX_BLOCK_SIZE) + 1;
        let mut free_lists: Vec<LinkedList<usize>> = Vec::with_capacity(num_levels);
        
        for _ in 0..num_levels {
            free_lists.push(LinkedList::new());
        }
        
        // 将整个内存池作为一个大块加入最高层级
        let max_level = num_levels - 1;
        free_lists[max_level].push_back(0);
        
        Self {
            pool,
            free_lists,
            used_bytes: 0,
            alloc_count: 0,
            free_count: 0,
        }
    }

    /// 将大小转换为层级索引
    fn size_to_level(size: usize) -> usize {
        let normalized = (size.max(MIN_BLOCK_SIZE) / MIN_BLOCK_SIZE).next_power_of_two();
        normalized.trailing_zeros() as usize
    }

    /// 将层级索引转换为块大小
    fn level_to_size(level: usize) -> usize {
        MIN_BLOCK_SIZE * (1 << level)
    }

    /// 获取块的伙伴地址
    fn get_buddy(&self, offset: usize, size: usize) -> usize {
        offset ^ size
    }

    /// 分配内存
    pub fn allocate(&mut self, size: usize) -> Option<usize> {
        if size == 0 || size > MAX_BLOCK_SIZE {
            return None;
        }

        // 计算所需层级（向上取整到2的幂）
        let required_level = Self::size_to_level(size);
        
        // 查找合适的块
        for level in required_level..self.free_lists.len() {
            if let Some(offset) = self.find_and_split(level, required_level) {
                self.used_bytes += Self::level_to_size(required_level);
                self.alloc_count += 1;
                return Some(offset);
            }
        }
        
        None // 内存不足
    }

    /// 查找并分割块
    fn find_and_split(&mut self, from_level: usize, to_level: usize) -> Option<usize> {
        if from_level == to_level {
            // 直接在目标层级查找
            return self.free_lists[from_level].pop_front();
        }

        // 尝试在更高层级查找
        if let Some(offset) = self.free_lists[from_level].pop_front() {
            // 递归分割
            let block_size = Self::level_to_size(from_level);
            let half_size = block_size / 2;
            
            // 将后半部分加入低一级链表
            let buddy_offset = offset + half_size;
            self.free_lists[from_level - 1].push_back(buddy_offset);
            
            // 递归分割前半部分
            self.free_lists[from_level - 1].push_front(offset);
            return self.find_and_split(from_level - 1, to_level);
        }
        
        None
    }

    /// 释放内存
    pub fn free(&mut self, offset: usize, size: usize) {
        if offset >= POOL_SIZE || size == 0 {
            return;
        }

        let level = Self::size_to_level(size);
        let block_size = Self::level_to_size(level);
        
        // 尝试合并伙伴块
        self.coalesce(offset, level);
        
        self.used_bytes -= block_size;
        self.free_count += 1;
    }

    /// 合并伙伴块
    fn coalesce(&mut self, mut offset: usize, mut level: usize) {
        let block_size = Self::level_to_size(level);
        let buddy = self.get_buddy(offset, block_size);

        // 检查伙伴是否在空闲链表中
        let mut found_buddy = false;
        let list = &mut self.free_lists[level];
        
        // 查找并移除伙伴
        if let Some(pos) = list.iter().position(|&x| x == buddy) {
            // 移除元素
            let mut temp: Vec<_> = std::mem::take(list).into_iter().collect();
            temp.remove(pos);
            *list = temp.into_iter().collect();
            found_buddy = true;
        }

        if found_buddy && level < self.free_lists.len() - 1 {
            // 找到伙伴，合并
            let merged_offset = offset.min(buddy);
            println!("  合并块: offset={}, buddy={}, level={}, 新偏移={}", 
                     offset, buddy, level, merged_offset);
            self.coalesce(merged_offset, level + 1);
        } else {
            // 未找到伙伴，将当前块加入空闲链表
            self.free_lists[level].push_back(offset);
        }
    }

    /// 获取内存使用统计
    pub fn stats(&self) -> AllocatorStats {
        let total_free: usize = self.free_lists.iter()
            .enumerate()
            .map(|(level, list)| {
                list.len() * Self::level_to_size(level)
            })
            .sum();

        AllocatorStats {
            total_bytes: POOL_SIZE,
            used_bytes: self.used_bytes,
            free_bytes: POOL_SIZE - self.used_bytes,
            alloc_count: self.alloc_count,
            free_count: self.free_count,
            fragmentation: 1.0 - (total_free as f64 / (POOL_SIZE - self.used_bytes) as f64),
        }
    }

    /// 打印空闲链表状态
    pub fn print_state(&self) {
        println!("\n=== 伙伴系统状态 ===");
        for (level, list) in self.free_lists.iter().enumerate() {
            let size = Self::level_to_size(level);
            if !list.is_empty() {
                println!("层级 {} ({} bytes): {} 个块, 偏移量 {:?}", 
                         level, size, list.len(), 
                         list.iter().collect::<Vec<_>>());
            }
        }
        let stats = self.stats();
        println!("已使用: {}/{} bytes ({:.1}%)", 
                 stats.used_bytes, stats.total_bytes,
                 (stats.used_bytes as f64 / stats.total_bytes as f64) * 100.0);
    }
}

/// 分配器统计信息
#[derive(Debug, Clone)]
pub struct AllocatorStats {
    pub total_bytes: usize,
    pub used_bytes: usize,
    pub free_bytes: usize,
    pub alloc_count: usize,
    pub free_count: usize,
    pub fragmentation: f64,
}

/// 简化的Slab分配器
/// 
/// Slab分配器专门用于分配固定大小的对象，减少内存碎片
pub struct SlabAllocator {
    /// 对象大小
    object_size: usize,
    /// 每页对象数
    objects_per_page: usize,
    /// 内存页
    pages: Vec<Vec<Option<u8>>>,
    /// 空闲对象列表
    free_list: Vec<(usize, usize)>, // (页索引, 对象索引)
    /// 已分配数量
    allocated: usize,
}

impl SlabAllocator {
    /// 创建新的 Slab 分配器
    pub fn new(object_size: usize, objects_per_page: usize) -> Self {
        Self {
            object_size,
            objects_per_page,
            pages: Vec::new(),
            free_list: Vec::new(),
            allocated: 0,
        }
    }

    /// 分配一个对象
    pub fn allocate(&mut self) -> Option<(usize, usize)> {
        // 首先尝试从空闲列表分配
        if let Some(slot) = self.free_list.pop() {
            self.allocated += 1;
            return Some(slot);
        }

        // 创建新页
        let page_idx = self.pages.len();
        let mut new_page: Vec<Option<u8>> = Vec::with_capacity(self.objects_per_page);
        
        for i in 0..self.objects_per_page {
            new_page.push(Some(0));
            if i > 0 {
                // 将其他对象加入空闲列表
                self.free_list.push((page_idx, i));
            }
        }
        
        self.pages.push(new_page);
        self.allocated += 1;
        
        // 返回第一个对象
        Some((page_idx, 0))
    }

    /// 释放对象
    pub fn free(&mut self, page_idx: usize, obj_idx: usize) {
        if page_idx < self.pages.len() && obj_idx < self.objects_per_page {
            self.free_list.push((page_idx, obj_idx));
            self.allocated -= 1;
        }
    }

    pub fn allocated_count(&self) -> usize {
        self.allocated
    }

    pub fn free_count(&self) -> usize {
        self.free_list.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_buddy_allocation() {
        let mut alloc = BuddyAllocator::new();
        
        // 分配不同大小的块
        let a = alloc.allocate(100).expect("分配失败");
        let b = alloc.allocate(200).expect("分配失败");
        let c = alloc.allocate(50).expect("分配失败");
        
        assert!(a != b && b != c);
        
        // 释放并重新分配
        alloc.free(b, 200);
        let d = alloc.allocate(200).expect("重新分配失败");
        
        // 可能得到相同的地址（如果合并成功）
        println!("b={}, d={}", b, d);
    }

    #[test]
    fn test_buddy_coalescing() {
        let mut alloc = BuddyAllocator::new();
        
        // 分配两个相邻的块
        let a = alloc.allocate(256).unwrap();
        let b = alloc.allocate(256).unwrap();
        
        alloc.print_state();
        
        // 释放两个块，它们应该合并
        alloc.free(a, 256);
        alloc.free(b, 256);
        
        alloc.print_state();
        
        // 现在应该能分配更大的块
        let c = alloc.allocate(512);
        assert!(c.is_some());
    }

    #[test]
    fn test_slab_allocator() {
        let mut slab = SlabAllocator::new(64, 10);
        
        let slots: Vec<_> = (0..15).map(|_| slab.allocate().unwrap()).collect();
        assert_eq!(slab.allocated_count(), 15);
        
        // 释放一些
        for (page, idx) in slots.iter().take(5) {
            slab.free(*page, *idx);
        }
        
        assert_eq!(slab.allocated_count(), 10);
        assert_eq!(slab.free_count(), 5);
    }
}

fn main() {
    println!("=== 伙伴系统分配器演示 ===");
    
    let mut alloc = BuddyAllocator::new();
    alloc.print_state();
    
    println!("\n分配 100 bytes...");
    let a = alloc.allocate(100).unwrap();
    println!("分配地址: {}", a);
    alloc.print_state();
    
    println!("\n分配 200 bytes...");
    let b = alloc.allocate(200).unwrap();
    println!("分配地址: {}", b);
    alloc.print_state();
    
    println!("\n分配 500 bytes...");
    let c = alloc.allocate(500).unwrap();
    println!("分配地址: {}", c);
    alloc.print_state();
    
    println!("\n释放 200 bytes (地址 {})...", b);
    alloc.free(b, 200);
    alloc.print_state();
    
    println!("\n释放 100 bytes (地址 {})...", a);
    alloc.free(a, 100);
    alloc.print_state();
    
    // 如果 a 和 b 是伙伴，释放后应该能分配更大的块
    println!("\n尝试分配 512 bytes...");
    if let Some(d) = alloc.allocate(512) {
        println!("成功分配 512 bytes 在地址 {}", d);
    }
    alloc.print_state();

    println!("\n=== Slab分配器演示 ===");
    let mut slab = SlabAllocator::new(64, 8);
    
    println!("分配对象...");
    let obj1 = slab.allocate().unwrap();
    let obj2 = slab.allocate().unwrap();
    println!("对象1: ({}, {}), 对象2: ({}, {})", obj1.0, obj1.1, obj2.0, obj2.1);
    println!("已分配: {}, 空闲: {}", slab.allocated_count(), slab.free_count());
    
    slab.free(obj1.0, obj1.1);
    println!("释放后 - 已分配: {}, 空闲: {}", slab.allocated_count(), slab.free_count());
}
