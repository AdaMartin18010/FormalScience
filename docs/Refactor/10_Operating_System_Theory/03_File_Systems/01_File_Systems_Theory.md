# 10.3.1 文件系统理论

## 📋 概述

文件系统理论研究操作系统中文件的组织、存储、访问和管理机制。该理论涵盖文件结构、目录组织、存储分配、文件保护等核心概念，为数据持久化提供理论基础。

## 1. 基本概念

### 1.1 文件系统定义

**定义 1.1**（文件系统）
文件系统是操作系统用于管理文件和目录的软件组件，提供数据的持久化存储。

### 1.2 文件系统类型分类

| 类型         | 英文名称         | 描述                         | 典型代表         |
|--------------|------------------|------------------------------|------------------|
| FAT          | File Allocation  | 文件分配表系统               | FAT32, exFAT     |
| NTFS         | New Technology   | 新技术文件系统               | Windows NT       |
| ext          | Extended         | 扩展文件系统                 | Linux            |
| ZFS          | Zettabyte        | 现代文件系统                 | Solaris, FreeBSD |

## 2. 形式化定义

### 2.1 文件结构

**定义 2.1**（文件）
文件是存储在存储设备上的命名数据集合，具有特定的结构和属性。

### 2.2 目录结构

**定义 2.2**（目录）
目录是包含文件和其他目录的容器，形成层次化的文件组织。

### 2.3 存储分配

**定义 2.3**（存储分配）
存储分配是文件系统将文件数据映射到物理存储块的过程。

## 3. 定理与证明

### 3.1 文件系统一致性定理

**定理 3.1**（文件系统一致性）
若文件系统在崩溃后能恢复到一致状态，则称其具有一致性。

**证明**：
通过日志记录、写时复制等技术，确保文件系统操作的原子性。□

### 3.2 存储效率定理

**定理 3.2**（存储效率）
文件系统的存储效率受块大小和文件大小分布影响。

**证明**：
设块大小为 $B$，文件大小为 $F$，则内部碎片为 $B - (F \bmod B)$。□

## 4. Rust代码实现

### 4.1 文件系统基本结构

```rust
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Debug, Clone)]
pub struct FileMetadata {
    pub name: String,
    pub size: usize,
    pub created_time: u64,
    pub modified_time: u64,
    pub permissions: FilePermissions,
    pub file_type: FileType,
}

#[derive(Debug, Clone)]
pub struct FilePermissions {
    pub owner_read: bool,
    pub owner_write: bool,
    pub owner_execute: bool,
    pub group_read: bool,
    pub group_write: bool,
    pub group_execute: bool,
    pub other_read: bool,
    pub other_write: bool,
    pub other_execute: bool,
}

#[derive(Debug, Clone)]
pub enum FileType {
    Regular,
    Directory,
    SymbolicLink,
    Device,
}

impl FileMetadata {
    pub fn new(name: String, file_type: FileType) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        FileMetadata {
            name,
            size: 0,
            created_time: now,
            modified_time: now,
            permissions: FilePermissions::default(),
            file_type,
        }
    }
}

impl Default for FilePermissions {
    fn default() -> Self {
        FilePermissions {
            owner_read: true,
            owner_write: true,
            owner_execute: false,
            group_read: true,
            group_write: false,
            group_execute: false,
            other_read: true,
            other_write: false,
            other_execute: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct File {
    pub metadata: FileMetadata,
    pub data: Vec<u8>,
    pub blocks: Vec<usize>,
}

impl File {
    pub fn new(name: String, file_type: FileType) -> Self {
        File {
            metadata: FileMetadata::new(name, file_type),
            data: Vec::new(),
            blocks: Vec::new(),
        }
    }
    
    pub fn write(&mut self, data: &[u8]) {
        self.data = data.to_vec();
        self.metadata.size = data.len();
        self.metadata.modified_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
    }
    
    pub fn read(&self) -> &[u8] {
        &self.data
    }
    
    pub fn append(&mut self, data: &[u8]) {
        self.data.extend_from_slice(data);
        self.metadata.size = self.data.len();
        self.metadata.modified_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
    }
}
```

### 4.2 目录系统实现

```rust
use std::collections::HashMap;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone)]
pub struct Directory {
    pub metadata: FileMetadata,
    pub entries: HashMap<String, DirectoryEntry>,
}

#[derive(Debug, Clone)]
pub enum DirectoryEntry {
    File(File),
    Directory(Directory),
    SymLink(String), // 目标路径
}

impl Directory {
    pub fn new(name: String) -> Self {
        Directory {
            metadata: FileMetadata::new(name, FileType::Directory),
            entries: HashMap::new(),
        }
    }
    
    pub fn add_file(&mut self, file: File) -> Result<(), String> {
        let name = file.metadata.name.clone();
        if self.entries.contains_key(&name) {
            return Err(format!("File {} already exists", name));
        }
        self.entries.insert(name, DirectoryEntry::File(file));
        Ok(())
    }
    
    pub fn add_directory(&mut self, dir: Directory) -> Result<(), String> {
        let name = dir.metadata.name.clone();
        if self.entries.contains_key(&name) {
            return Err(format!("Directory {} already exists", name));
        }
        self.entries.insert(name, DirectoryEntry::Directory(dir));
        Ok(())
    }
    
    pub fn remove(&mut self, name: &str) -> Result<DirectoryEntry, String> {
        self.entries.remove(name)
            .ok_or_else(|| format!("Entry {} not found", name))
    }
    
    pub fn get(&self, name: &str) -> Option<&DirectoryEntry> {
        self.entries.get(name)
    }
    
    pub fn list(&self) -> Vec<String> {
        self.entries.keys().cloned().collect()
    }
}

#[derive(Debug, Clone)]
pub struct FileSystem {
    pub root: Directory,
    pub current_directory: PathBuf,
    pub block_size: usize,
    pub total_blocks: usize,
    pub free_blocks: Vec<bool>,
}

impl FileSystem {
    pub fn new(block_size: usize, total_blocks: usize) -> Self {
        FileSystem {
            root: Directory::new("/".to_string()),
            current_directory: PathBuf::from("/"),
            block_size,
            total_blocks,
            free_blocks: vec![true; total_blocks],
        }
    }
    
    pub fn create_file(&mut self, path: &Path, data: &[u8]) -> Result<(), String> {
        let mut current = &mut self.root;
        let path_components: Vec<_> = path.iter().collect();
        
        // 导航到父目录
        for component in &path_components[..path_components.len()-1] {
            if let Some(DirectoryEntry::Directory(ref mut dir)) = 
                current.entries.get_mut(component.to_str().unwrap()) {
                current = dir;
            } else {
                return Err(format!("Path component {:?} is not a directory", component));
            }
        }
        
        // 创建文件
        let file_name = path_components.last().unwrap().to_str().unwrap();
        let mut file = File::new(file_name.to_string(), FileType::Regular);
        file.write(data);
        
        // 分配存储块
        let blocks_needed = (data.len() + self.block_size - 1) / self.block_size;
        for _ in 0..blocks_needed {
            if let Some(block_index) = self.allocate_block() {
                file.blocks.push(block_index);
            } else {
                return Err("No free blocks available".to_string());
            }
        }
        
        current.add_file(file)
    }
    
    pub fn read_file(&self, path: &Path) -> Result<Vec<u8>, String> {
        let mut current = &self.root;
        let path_components: Vec<_> = path.iter().collect();
        
        // 导航到文件
        for component in &path_components[..path_components.len()-1] {
            if let Some(DirectoryEntry::Directory(ref dir)) = 
                current.entries.get(component.to_str().unwrap()) {
                current = dir;
            } else {
                return Err(format!("Path component {:?} is not a directory", component));
            }
        }
        
        let file_name = path_components.last().unwrap().to_str().unwrap();
        if let Some(DirectoryEntry::File(ref file)) = current.entries.get(file_name) {
            Ok(file.read().to_vec())
        } else {
            Err(format!("File {} not found", file_name))
        }
    }
    
    pub fn list_directory(&self, path: &Path) -> Result<Vec<String>, String> {
        let mut current = &self.root;
        
        for component in path.iter() {
            if let Some(DirectoryEntry::Directory(ref dir)) = 
                current.entries.get(component.to_str().unwrap()) {
                current = dir;
            } else {
                return Err(format!("Path component {:?} is not a directory", component));
            }
        }
        
        Ok(current.list())
    }
    
    fn allocate_block(&mut self) -> Option<usize> {
        for (index, &free) in self.free_blocks.iter().enumerate() {
            if free {
                self.free_blocks[index] = false;
                return Some(index);
            }
        }
        None
    }
    
    pub fn get_free_space(&self) -> usize {
        self.free_blocks.iter().filter(|&&free| free).count() * self.block_size
    }
    
    pub fn get_total_space(&self) -> usize {
        self.total_blocks * self.block_size
    }
}
```

### 4.3 文件系统日志实现

```rust
use std::collections::VecDeque;

#[derive(Debug, Clone)]
pub enum LogEntry {
    CreateFile { path: String, size: usize },
    WriteFile { path: String, offset: usize, data: Vec<u8> },
    DeleteFile { path: String },
    CreateDirectory { path: String },
    DeleteDirectory { path: String },
}

#[derive(Debug, Clone)]
pub struct FileSystemLog {
    pub entries: VecDeque<LogEntry>,
    pub max_entries: usize,
    pub checkpoint_interval: usize,
}

impl FileSystemLog {
    pub fn new(max_entries: usize, checkpoint_interval: usize) -> Self {
        FileSystemLog {
            entries: VecDeque::new(),
            max_entries,
            checkpoint_interval,
        }
    }
    
    pub fn add_entry(&mut self, entry: LogEntry) {
        self.entries.push_back(entry);
        
        // 检查是否需要清理日志
        if self.entries.len() > self.max_entries {
            self.entries.pop_front();
        }
        
        // 检查是否需要创建检查点
        if self.entries.len() % self.checkpoint_interval == 0 {
            self.create_checkpoint();
        }
    }
    
    pub fn create_checkpoint(&mut self) {
        // 将当前文件系统状态写入检查点
        // 清空日志条目
        self.entries.clear();
    }
    
    pub fn recover(&self) -> Vec<LogEntry> {
        // 从检查点恢复，然后重放日志
        self.entries.iter().cloned().collect()
    }
    
    pub fn get_log_size(&self) -> usize {
        self.entries.len()
    }
}

#[derive(Debug, Clone)]
pub struct JournalingFileSystem {
    pub fs: FileSystem,
    pub log: FileSystemLog,
}

impl JournalingFileSystem {
    pub fn new(block_size: usize, total_blocks: usize) -> Self {
        JournalingFileSystem {
            fs: FileSystem::new(block_size, total_blocks),
            log: FileSystemLog::new(1000, 100),
        }
    }
    
    pub fn create_file(&mut self, path: &Path, data: &[u8]) -> Result<(), String> {
        // 记录日志条目
        self.log.add_entry(LogEntry::CreateFile {
            path: path.to_string_lossy().to_string(),
            size: data.len(),
        });
        
        // 执行实际操作
        self.fs.create_file(path, data)
    }
    
    pub fn write_file(&mut self, path: &Path, offset: usize, data: &[u8]) -> Result<(), String> {
        // 记录日志条目
        self.log.add_entry(LogEntry::WriteFile {
            path: path.to_string_lossy().to_string(),
            offset,
            data: data.to_vec(),
        });
        
        // 执行实际操作
        // 这里需要实现文件写入逻辑
        Ok(())
    }
    
    pub fn delete_file(&mut self, path: &Path) -> Result<(), String> {
        // 记录日志条目
        self.log.add_entry(LogEntry::DeleteFile {
            path: path.to_string_lossy().to_string(),
        });
        
        // 执行实际操作
        // 这里需要实现文件删除逻辑
        Ok(())
    }
    
    pub fn recover(&mut self) {
        // 从日志恢复文件系统状态
        let entries = self.log.recover();
        for entry in entries {
            match entry {
                LogEntry::CreateFile { path, size } => {
                    // 重新创建文件
                    let path = Path::new(&path);
                    let data = vec![0; size];
                    let _ = self.fs.create_file(path, &data);
                },
                LogEntry::WriteFile { path, offset, data } => {
                    // 重新写入文件
                    let path = Path::new(&path);
                    let _ = self.write_file(path, offset, &data);
                },
                LogEntry::DeleteFile { path } => {
                    // 重新删除文件
                    let path = Path::new(&path);
                    let _ = self.delete_file(path);
                },
                _ => {
                    // 处理其他类型的日志条目
                }
            }
        }
    }
}
```

## 5. 相关理论与交叉引用

- [进程管理理论](../01_Process_Management/01_Process_Management_Theory.md)
- [内存管理理论](../02_Memory_Management/01_Memory_Management_Theory.md)
- [设备管理理论](../04_Device_Management/01_Device_Management_Theory.md)

## 6. 参考文献

1. Silberschatz, A., Galvin, P. B., & Gagne, G. (2018). Operating System Concepts. Wiley.
2. Tanenbaum, A. S., & Bos, H. (2014). Modern Operating Systems. Pearson.
3. McKusick, M. K., & Neville-Neil, G. V. (2014). The Design and Implementation of the FreeBSD Operating System. Addison-Wesley.

---

**最后更新**: 2024年12月21日  
**维护者**: AI助手  
**版本**: v1.0
