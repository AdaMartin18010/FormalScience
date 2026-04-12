//! # 线性类型系统实现
//! 
//! 线性类型确保资源只能被使用一次，展示 Rust 的所有权系统如何
//! 实现线性类型的概念。

use std::ops::Drop;

/// 线性资源：只能被使用一次的资源
pub struct LinearResource<T> {
    value: Option<T>,
    name: String,
}

impl<T> LinearResource<T> {
    /// 创建一个新的线性资源
    pub fn new(value: T, name: impl Into<String>) -> Self {
        Self {
            value: Some(value),
            name: name.into(),
        }
    }

    /// 消费资源，返回其值
    /// 此方法获取 self 的所有权，确保资源只能被使用一次
    pub fn consume(mut self) -> T {
        self.value
            .take()
            .expect("Resource already consumed")
    }

    /// 检查资源是否已被消费
    pub fn is_available(&self) -> bool {
        self.value.is_some()
    }

    /// 获取资源名称
    pub fn name(&self) -> &str {
        &self.name
    }

    /// 使用资源进行一个操作，然后返回资源
    /// 这允许链式使用，但最终资源仍必须被消费
    pub fn map<U, F>(mut self, f: F) -> LinearResource<U>
    where
        F: FnOnce(T) -> U,
    {
        let value = self.value
            .take()
            .expect("Resource already consumed");
        LinearResource::new(f(value), self.name.clone())
    }
}

impl<T> Drop for LinearResource<T> {
    fn drop(&mut self) {
        if self.value.is_some() {
            panic!(
                "LinearResource '{}' was dropped without being consumed!",
                self.name
            );
        }
    }
}

/// 文件句柄：线性类型的实际应用示例
pub struct FileHandle {
    path: String,
    is_open: bool,
}

impl FileHandle {
    /// 打开文件
    pub fn open(path: impl Into<String>) -> Result<Self, FileError> {
        let path = path.into();
        // 模拟文件打开操作
        Ok(Self {
            path,
            is_open: true,
        })
    }

    /// 读取文件内容（消耗所有权）
    pub fn read(self) -> Result<(String, Self), FileError> {
        if !self.is_open {
            return Err(FileError::AlreadyClosed);
        }
        // 模拟读取操作
        let content = format!("Content of {}", self.path);
        Ok((content, self))
    }

    /// 写入内容到文件（消耗所有权）
    pub fn write(self, content: impl AsRef<str>) -> Result<Self, FileError> {
        if !self.is_open {
            return Err(FileError::AlreadyClosed);
        }
        // 模拟写入操作
        println!("Writing '{}' to {}", content.as_ref(), self.path);
        Ok(self)
    }

    /// 关闭文件（必须显式调用）
    pub fn close(mut self) {
        self.is_open = false;
        // 忘记 self，避免调用 Drop 的 panic
        std::mem::forget(self);
    }

    /// 获取文件路径
    pub fn path(&self) -> &str {
        &self.path
    }
}

impl Drop for FileHandle {
    fn drop(&mut self) {
        if self.is_open {
            panic!(
                "FileHandle for '{}' was dropped without being closed!",
                self.path
            );
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum FileError {
    AlreadyClosed,
    IoError(String),
}

/// 独占引用示例：展示借用检查器
pub struct ExclusiveRef<'a, T> {
    data: &'a mut T,
}

impl<'a, T> ExclusiveRef<'a, T> {
    pub fn new(data: &'a mut T) -> Self {
        Self { data }
    }

    pub fn get(&self) -> &T {
        self.data
    }

    pub fn get_mut(&mut self) -> &mut T {
        self.data
    }

    pub fn modify<F>(&mut self, f: F)
    where
        F: FnOnce(&mut T),
    {
        f(self.data);
    }
}

/// 共享引用示例：不可变借用
pub struct SharedRef<'a, T> {
    data: &'a T,
}

impl<'a, T> SharedRef<'a, T> {
    pub fn new(data: &'a T) -> Self {
        Self { data }
    }

    pub fn get(&self) -> &T {
        self.data
    }

    /// 可以创建多个共享引用
    pub fn share(&self) -> SharedRef<'_, T> {
        SharedRef::new(self.data)
    }
}

/// 资源池：管理有限资源
pub struct ResourcePool<T> {
    available: Vec<T>,
    in_use: Vec<T>,
}

impl<T> ResourcePool<T> {
    pub fn new(resources: Vec<T>) -> Self {
        Self {
            available: resources,
            in_use: Vec::new(),
        }
    }

    /// 获取一个资源（如果可用）
    pub fn acquire(&mut self) -> Option<PooledResource<T>> {
        self.available.pop().map(|res| {
            self.in_use.push(unsafe { std::ptr::read(&res) });
            PooledResource {
                resource: Some(res),
                pool_ptr: self as *mut _,
            }
        })
    }

    /// 返回可用资源数量
    pub fn available_count(&self) -> usize {
        self.available.len()
    }

    /// 返回使用中资源数量
    pub fn in_use_count(&self) -> usize {
        self.in_use.len()
    }

    fn release(&mut self, resource: T) {
        // 从 in_use 中移除（简化处理）
        self.available.push(resource);
    }
}

/// 池化资源：确保资源返回到池中
pub struct PooledResource<T> {
    resource: Option<T>,
    pool_ptr: *mut ResourcePool<T>,
}

impl<T> PooledResource<T> {
    pub fn get(&self) -> &T {
        self.resource.as_ref().unwrap()
    }

    pub fn get_mut(&mut self) -> &mut T {
        self.resource.as_mut().unwrap()
    }
}

impl<T> Drop for PooledResource<T> {
    fn drop(&mut self) {
        if let Some(resource) = self.resource.take() {
            unsafe {
                (*self.pool_ptr).release(resource);
            }
        }
    }
}

// 不安全：确保 PooledResource 不会比 ResourcePool 活得更长
unsafe impl<T: Send> Send for PooledResource<T> {}
unsafe impl<T: Sync> Sync for PooledResource<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linear_resource() {
        let resource = LinearResource::new(42, "test_resource");
        assert!(resource.is_available());
        
        let value = resource.consume();
        assert_eq!(value, 42);
    }

    #[test]
    fn test_linear_resource_map() {
        let resource = LinearResource::new(5, "number");
        let mapped = resource.map(|x| x * 2);
        
        assert_eq!(mapped.consume(), 10);
    }

    #[test]
    fn test_file_handle() {
        let file = FileHandle::open("test.txt").unwrap();
        let (content, file) = file.read().unwrap();
        assert_eq!(content, "Content of test.txt");
        file.close();
    }

    #[test]
    fn test_file_handle_write() {
        let file = FileHandle::open("test.txt").unwrap();
        let file = file.write("Hello, World!").unwrap();
        file.close();
    }

    #[test]
    fn test_exclusive_ref() {
        let mut data = 42;
        {
            let mut excl = ExclusiveRef::new(&mut data);
            excl.modify(|x| *x += 1);
            assert_eq!(*excl.get(), 43);
        }
        assert_eq!(data, 43);
    }

    #[test]
    fn test_shared_ref() {
        let data = 42;
        let shared1 = SharedRef::new(&data);
        let shared2 = shared1.share();
        
        assert_eq!(*shared1.get(), 42);
        assert_eq!(*shared2.get(), 42);
    }

    #[test]
    fn test_resource_pool() {
        let mut pool = ResourcePool::new(vec![1, 2, 3]);
        assert_eq!(pool.available_count(), 3);
        
        {
            let mut res = pool.acquire().unwrap();
            assert_eq!(*res.get(), 3);
            *res.get_mut() = 10;
        }
        
        // 资源应该被归还
        assert_eq!(pool.available_count(), 3);
    }
}
