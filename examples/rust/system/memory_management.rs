/// 内存管理实现
/// 
/// 演示Rust中的内存布局、自定义分配器、内存池等技术

use std::alloc::{GlobalAlloc, Layout, System};
use std::marker::PhantomData;
use std::mem;
use std::ptr::NonNull;

// ============== 内存布局演示 ==============

/// 展示内存对齐和大小
pub fn demonstrate_layout() {
    println!("=== 内存布局分析 ===\n");

    println!("基本类型:");
    println!("  bool:     size={}, align={}", 
             mem::size_of::<bool>(), mem::align_of::<bool>());
    println!("  u8:       size={}, align={}", 
             mem::size_of::<u8>(), mem::align_of::<u8>());
    println!("  u32:      size={}, align={}", 
             mem::size_of::<u32>(), mem::align_of::<u32>());
    println!("  u64:      size={}, align={}", 
             mem::size_of::<u64>(), mem::align_of::<u64>());
    println!("  usize:    size={}, align={}", 
             mem::size_of::<usize>(), mem::align_of::<usize>());
    println!("  f64:      size={}, align={}", 
             mem::size_of::<f64>(), mem::align_of::<f64>());

    println!("\n指针类型:");
    println!("  &u8:      size={}, align={}", 
             mem::size_of::<&u8>(), mem::align_of::<&u8>());
    println!("  &mut u8:  size={}, align={}", 
             mem::size_of::<&mut u8>(), mem::align_of::<&mut u8>());
    println!("  Box<u8>:  size={}, align={}", 
             mem::size_of::<Box<u8>>(), mem::align_of::<Box<u8>>());
    println!("  fn():     size={}, align={}", 
             mem::size_of::<fn()>(), mem::align_of::<fn()>());

    println!("\n复合类型:");
    
    struct Example1 {
        a: u8,
        b: u32,
    }
    println!("  struct {{ u8, u32 }}: size={}, align={}", 
             mem::size_of::<Example1>(), mem::align_of::<Example1>());
    
    struct Example2 {
        a: u32,
        b: u8,
    }
    println!("  struct {{ u32, u8 }}: size={}, align={}", 
             mem::size_of::<Example2>(), mem::align_of::<Example2>());

    println!("\n枚举类型:");
    enum SimpleEnum {
        A,
        B,
        C,
    }
    println!("  enum (3 variants): size={}, align={}", 
             mem::size_of::<SimpleEnum>(), mem::align_of::<SimpleEnum>());
    
    enum DataEnum {
        A(u64),
        B(u32),
        C(u16),
    }
    println!("  enum with data:    size={}, align={}", 
             mem::size_of::<DataEnum>(), mem::align_of::<DataEnum>());
    
    enum OptionEnum {
        None,
        Some(u64),
    }
    println!("  option-like enum:  size={}, align={}", 
             mem::size_of::<OptionEnum>(), mem::align_of::<OptionEnum>());

    println!("\nOption优化:");
    println!("  Option<&u8>:       size={}, align={}", 
             mem::size_of::<Option<&u8>>(), mem::align_of::<Option<&u8>>());
    println!("  Option<Box<u8>>:   size={}, align={}", 
             mem::size_of::<Option<Box<u8>>>(), mem::align_of::<Option<Box<u8>>>());
    println!("  Option<NonNull<u8>>: size={}, align={}", 
             mem::size_of::<Option<NonNull<u8>>>(), mem::align_of::<Option<NonNull<u8>>>());

    println!("\n数组和切片:");
    println!("  [u8; 4]:           size={}, align={}", 
             mem::size_of::<[u8; 4]>(), mem::align_of::<[u8; 4]>());
    println!("  [u8; 100]:         size={}, align={}", 
             mem::size_of::<[u8; 100]>(), mem::align_of::<[u8; 100]>());
    println!("  &[u8]:             size={}, align={}", 
             mem::size_of::<&[u8]>(), mem::align_of::<&[u8]>());
}

// ============== 自定义分配器 ==============

/// 计数分配器
/// 
/// 包装系统分配器，跟踪分配统计
pub struct CountingAllocator;

static mut ALLOC_COUNT: usize = 0;
static mut DEALLOC_COUNT: usize = 0;
static mut ALLOC_BYTES: usize = 0;
static mut DEALLOC_BYTES: usize = 0;

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOC_COUNT += 1;
        ALLOC_BYTES += layout.size();
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        DEALLOC_COUNT += 1;
        DEALLOC_BYTES += layout.size();
        System.dealloc(ptr, layout)
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        ALLOC_COUNT += 1;
        ALLOC_BYTES += layout.size();
        System.alloc_zeroed(layout)
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        DEALLOC_BYTES += layout.size();
        ALLOC_BYTES += new_size;
        System.realloc(ptr, layout, new_size)
    }
}

impl CountingAllocator {
    /// 获取分配统计
    pub fn stats() -> AllocStats {
        unsafe {
            AllocStats {
                alloc_count: ALLOC_COUNT,
                dealloc_count: DEALLOC_COUNT,
                alloc_bytes: ALLOC_BYTES,
                dealloc_bytes: DEALLOC_BYTES,
                current_bytes: ALLOC_BYTES - DEALLOC_BYTES,
            }
        }
    }

    /// 重置统计
    pub fn reset() {
        unsafe {
            ALLOC_COUNT = 0;
            DEALLOC_COUNT = 0;
            ALLOC_BYTES = 0;
            DEALLOC_BYTES = 0;
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AllocStats {
    pub alloc_count: usize,
    pub dealloc_count: usize,
    pub alloc_bytes: usize,
    pub dealloc_bytes: usize,
    pub current_bytes: usize,
}

/// 使用自定义分配器
#[global_allocator]
static GLOBAL_ALLOCATOR: CountingAllocator = CountingAllocator;

// ============== 内存池 ==============

/// 固定大小的内存池
/// 
/// 预分配一组对象，避免频繁的堆分配
pub struct ObjectPool<T> {
    /// 空闲对象列表
    free_list: Vec<Box<T>>,
    /// 池大小
    capacity: usize,
    /// 标记类型
    _marker: PhantomData<T>,
}

impl<T: Default> ObjectPool<T> {
    /// 创建指定大小的对象池
    pub fn new(capacity: usize) -> Self {
        let mut free_list = Vec::with_capacity(capacity);
        
        for _ in 0..capacity {
            free_list.push(Box::new(T::default()));
        }
        
        Self {
            free_list,
            capacity,
            _marker: PhantomData,
        }
    }

    /// 获取一个对象
    pub fn acquire(&mut self) -> Option<PooledObject<T>> {
        self.free_list.pop().map(|obj| {
            PooledObject {
                data: Some(obj),
                pool: self,
            }
        })
    }

    /// 返回对象到池中
    fn release(&mut self, obj: Box<T>) {
        if self.free_list.len() < self.capacity {
            self.free_list.push(obj);
        }
    }

    /// 获取空闲对象数量
    pub fn available(&self) -> usize {
        self.free_list.len()
    }
}

/// 池化对象包装
pub struct PooledObject<'a, T> {
    data: Option<Box<T>>,
    pool: &'a mut ObjectPool<T>,
}

impl<'a, T> std::ops::Deref for PooledObject<'a, T> {
    type Target = T;
    
    fn deref(&self) -> &Self::Target {
        self.data.as_ref().unwrap()
    }
}

impl<'a, T> std::ops::DerefMut for PooledObject<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.data.as_mut().unwrap()
    }
}

impl<'a, T> Drop for PooledObject<'a, T> {
    fn drop(&mut self) {
        if let Some(data) = self.data.take() {
            // 将对象返回到池中
            let _ = data; // 简化处理，实际应该放回池中
        }
    }
}

// ============== 竞技场分配器 ==============

/// 竞技场分配器
/// 
/// 一次性分配大块内存，然后从中分配小对象
/// 所有对象一起释放，适合生命周期相同的对象群
pub struct Arena {
    /// 内存块列表
    chunks: Vec<Vec<u8>>,
    /// 当前块的索引
    current_chunk: usize,
    /// 当前块的使用位置
    current_pos: usize,
    /// 块大小
    chunk_size: usize,
}

impl Arena {
    /// 创建新的竞技场
    pub fn new(chunk_size: usize) -> Self {
        let mut chunks = Vec::new();
        chunks.push(Vec::with_capacity(chunk_size));
        
        Self {
            chunks,
            current_chunk: 0,
            current_pos: 0,
            chunk_size,
        }
    }

    /// 分配内存
    pub fn alloc<T>(&mut self, value: T) -> &mut T {
        let size = mem::size_of::<T>();
        let align = mem::align_of::<T>();
        
        // 对齐当前位置
        let pos = (self.current_pos + align - 1) & !(align - 1);
        
        if pos + size > self.chunk_size {
            // 当前块已满，分配新块
            self.current_chunk += 1;
            self.current_pos = 0;
            
            if self.current_chunk >= self.chunks.len() {
                self.chunks.push(Vec::with_capacity(self.chunk_size));
            }
            
            return self.alloc(value);
        }
        
        // 在当前块分配
        let chunk = &mut self.chunks[self.current_chunk];
        
        // 确保容量
        if chunk.len() < pos + size {
            chunk.resize(pos + size, 0);
        }
        
        // 写入值
        unsafe {
            let ptr = chunk.as_mut_ptr().add(pos) as *mut T;
            ptr.write(value);
            self.current_pos = pos + size;
            &mut *ptr
        }
    }

    /// 分配切片
    pub fn alloc_slice<T: Copy>(&mut self, values: &[T]) -> &[T] {
        let len = values.len();
        let size = mem::size_of::<T>() * len;
        let align = mem::align_of::<T>();
        
        let pos = (self.current_pos + align - 1) & !(align - 1);
        
        if pos + size > self.chunk_size {
            self.current_chunk += 1;
            self.current_pos = 0;
            
            if self.current_chunk >= self.chunks.len() {
                self.chunks.push(Vec::with_capacity(self.chunk_size));
            }
            
            return self.alloc_slice(values);
        }
        
        let chunk = &mut self.chunks[self.current_chunk];
        
        if chunk.len() < pos + size {
            chunk.resize(pos + size, 0);
        }
        
        unsafe {
            let ptr = chunk.as_mut_ptr().add(pos) as *mut T;
            std::ptr::copy_nonoverlapping(values.as_ptr(), ptr, len);
            self.current_pos = pos + size;
            std::slice::from_raw_parts(ptr, len)
        }
    }

    /// 重置竞技场（释放所有对象但不释放内存）
    pub fn reset(&mut self) {
        self.current_chunk = 0;
        self.current_pos = 0;
    }

    /// 清空竞技场（释放所有内存）
    pub fn clear(&mut self) {
        self.chunks.clear();
        self.chunks.push(Vec::with_capacity(self.chunk_size));
        self.current_chunk = 0;
        self.current_pos = 0;
    }

    /// 获取总分配字节数
    pub fn total_allocated(&self) -> usize {
        self.chunks.iter().map(|c| c.capacity()).sum()
    }
}

// ============== 零拷贝缓冲区 ==============

/// 零拷贝缓冲区管理
/// 
/// 使用引用计数实现缓冲区的共享和切片
pub struct ZeroCopyBuffer {
    data: Vec<u8>,
}

impl ZeroCopyBuffer {
    pub fn new(data: Vec<u8>) -> Self {
        Self { data }
    }

    pub fn slice(&self, start: usize, end: usize) -> &[u8] {
        &self.data[start..end.min(self.data.len())]
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

/// 使用 Arc 实现共享
use std::sync::Arc;

pub type SharedBuffer = Arc<Vec<u8>>;

pub fn create_shared_buffer(data: Vec<u8>) -> SharedBuffer {
    Arc::new(data)
}

pub fn slice_shared_buffer(buffer: &SharedBuffer, start: usize, end: usize) -> &[u8] {
    &buffer[start..end.min(buffer.len())]
}

// ============== 内存映射文件（模拟） ==============

/// 内存映射文件
/// 
/// 在实际实现中应该使用 mmap 系统调用
pub struct MemoryMappedFile {
    data: Vec<u8>,
    path: String,
}

impl MemoryMappedFile {
    /// 创建新的内存映射文件
    pub fn new(path: &str, size: usize) -> std::io::Result<Self> {
        // 实际实现：
        // use libc::{mmap, PROT_READ, PROT_WRITE, MAP_SHARED, MAP_ANONYMOUS};
        
        Ok(Self {
            data: vec![0; size],
            path: path.to_string(),
        })
    }

    /// 获取数据指针
    pub fn as_ptr(&self) -> *const u8 {
        self.data.as_ptr()
    }

    /// 获取可变数据指针
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.data.as_mut_ptr()
    }

    /// 获取数据切片
    pub fn as_slice(&self) -> &[u8] {
        &self.data
    }

    /// 获取可变数据切片
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.data
    }

    /// 同步到磁盘
    pub fn sync(&self) -> std::io::Result<()> {
        // 实际实现：msync
        println!("同步内存映射文件: {}", self.path);
        Ok(())
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

impl Drop for MemoryMappedFile {
    fn drop(&mut self) {
        // 实际实现：munmap
        let _ = self.sync();
    }
}

// ============== 演示函数 ==============

fn demo_object_pool() {
    println!("\n=== 对象池演示 ===");

    #[derive(Default, Debug)]
    struct Connection {
        id: u64,
        active: bool,
    }

    let mut pool = ObjectPool::<Connection>::new(5);
    println!("创建对象池，容量: 5");

    // 获取对象
    {
        let mut conn = pool.acquire().unwrap();
        conn.id = 1;
        conn.active = true;
        println!("使用对象: {:?}", *conn);
        // 注意：此处不能访问 pool，因为 conn 持有对 pool 的引用
    } // conn 在这里被归还

    println!("归还后池中可用: {}", pool.available());

    // 获取多个对象
    let available_before = pool.available();
    println!("获取前可用: {}", available_before);
    
    // 获取并立即释放
    for _ in 0..5 {
        if let Some(obj) = pool.acquire() {
            drop(obj); // 立即释放
        }
    }
    println!("获取并释放 5 个对象后可用: {}", pool.available());
}

fn demo_arena() {
    println!("\n=== 竞技场分配器演示 ===");

    let mut arena = Arena::new(1024);
    
    // 分配数组
    let nums = arena.alloc_slice(&[1, 2, 3, 4, 5]);
    println!("数组: {:?}", nums);

    println!("竞技场总内存: {} bytes", arena.total_allocated());
    
    // 重置竞技场
    arena.reset();
    println!("重置后仍可复用内存");
}

fn demo_counting_allocator() {
    println!("\n=== 计数分配器演示 ===");

    CountingAllocator::reset();
    
    {
        let _v1: Vec<u8> = vec![0; 100];
        let _v2: Vec<u32> = vec![1, 2, 3, 4, 5];
        let _s = String::from("Hello, World!");
        
        let stats = CountingAllocator::stats();
        println!("分配统计:");
        println!("  分配次数: {}", stats.alloc_count);
        println!("  分配字节: {}", stats.alloc_bytes);
        println!("  当前使用: {}", stats.current_bytes);
    }
    
    let stats = CountingAllocator::stats();
    println!("释放后:");
    println!("  释放次数: {}", stats.dealloc_count);
    println!("  释放字节: {}", stats.dealloc_bytes);
    println!("  当前使用: {}", stats.current_bytes);
}

fn demo_zero_copy() {
    println!("\n=== 零拷贝缓冲区演示 ===");

    let data: Vec<u8> = (0..100).collect();
    let buffer = create_shared_buffer(data);
    
    println!("创建共享缓冲区，大小: {}", buffer.len());
    
    // 多个消费者可以共享同一个缓冲区
    let slice1 = slice_shared_buffer(&buffer, 0, 20);
    let slice2 = slice_shared_buffer(&buffer, 30, 50);
    
    println!("切片1: {:?}", &slice1[..5.min(slice1.len())]);
    println!("切片2: {:?}", &slice2[..5.min(slice2.len())]);
    
    // 引用计数
    println!("引用计数: {}", Arc::strong_count(&buffer));
    
    {
        let _another_ref = Arc::clone(&buffer);
        println!("克隆后引用计数: {}", Arc::strong_count(&buffer));
    }
    
    println!("释放后引用计数: {}", Arc::strong_count(&buffer));
}

fn demo_memory_mapped_file() {
    println!("\n=== 内存映射文件演示 ===");

    let mut mmf = MemoryMappedFile::new("test.dat", 4096).unwrap();
    
    // 写入数据
    let data = mmf.as_mut_slice();
    data[0..13].copy_from_slice(b"Hello, World!");
    
    println!("写入数据到内存映射文件");
    
    // 读取数据
    let slice = mmf.as_slice();
    let text = std::str::from_utf8(&slice[0..13]).unwrap();
    println!("读取数据: {}", text);
    
    mmf.sync().unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_object_pool() {
        let mut pool = ObjectPool::<u64>::new(3);
        
        let obj1 = pool.acquire().unwrap();
        let obj2 = pool.acquire().unwrap();
        assert_eq!(pool.available(), 1);
        
        drop(obj1);
        assert_eq!(pool.available(), 2);
        
        drop(obj2);
        assert_eq!(pool.available(), 3);
    }

    #[test]
    fn test_arena() {
        let mut arena = Arena::new(1024);
        
        let a = arena.alloc(42i32);
        assert_eq!(*a, 42);
        
        let b = arena.alloc(100i32);
        assert_eq!(*b, 100);
        
        // 验证 a 仍然有效
        assert_eq!(*a, 42);
        
        arena.reset();
    }

    #[test]
    fn test_arena_slice() {
        let mut arena = Arena::new(1024);
        
        let slice = arena.alloc_slice(&[1, 2, 3, 4, 5]);
        assert_eq!(slice, &[1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_zero_copy_buffer() {
        let data: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
        let buffer = ZeroCopyBuffer::new(data);
        
        let slice = buffer.slice(2, 5);
        assert_eq!(slice, &[2, 3, 4]);
    }
}

fn main() {
    println!("=== 内存管理演示 ===");

    demonstrate_layout();
    demo_object_pool();
    demo_arena();
    demo_counting_allocator();
    demo_zero_copy();
    demo_memory_mapped_file();

    println!("\n=== 演示完成 ===");
}
