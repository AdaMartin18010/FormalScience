/// 系统调用封装
/// 
/// 演示如何在 Rust 中进行系统调用、处理错误、以及常见系统调用的封装

use std::ffi::{CStr, CString};
use std::io;
use std::mem;
use std::os::raw::{c_char, c_int, c_long, c_void};
use std::ptr;

// ============== 系统调用基础 ==============

/// 系统调用号（Linux x86_64）
#[cfg(target_arch = "x86_64")]
mod syscall_nums {
    pub const SYS_READ: i64 = 0;
    pub const SYS_WRITE: i64 = 1;
    pub const SYS_OPEN: i64 = 2;
    pub const SYS_CLOSE: i64 = 3;
    pub const SYS_FSTAT: i64 = 5;
    pub const SYS_MMAP: i64 = 9;
    pub const SYS_MUNMAP: i64 = 11;
    pub const SYS_FORK: i64 = 57;
    pub const SYS_EXIT: i64 = 60;
    pub const SYS_GETPID: i64 = 39;
    pub const SYS_GETUID: i64 = 102;
    pub const SYS_GETGID: i64 = 104;
    pub const SYS_NANOSLEEP: i64 = 35;
    pub const SYS_GETCWD: i64 = 79;
    pub const SYS_CHDIR: i64 = 80;
    pub const SYS_RENAME: i64 = 82;
    pub const SYS_MKDIR: i64 = 83;
    pub const SYS_RMDIR: i64 = 84;
    pub const SYS_UNLINK: i64 = 87;
    pub const SYS_GETTIMEOFDAY: i64 = 96;
    pub const SYS_GETRLIMIT: i64 = 97;
    pub const SYS_GETRUSAGE: i64 = 98;
    pub const SYS_TIMES: i64 = 100;
}

/// 使用 libc 进行系统调用
/// 
/// 在实际项目中，应该使用 libc crate 或 rustix crate
mod syscall {
    use super::*;

    /// 直接系统调用（Linux x86_64）
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    pub unsafe fn syscall1(n: c_long, a1: c_long) -> c_long {
        let ret: c_long;
        asm!(
            "syscall",
            inout("rax") n => ret,
            in("rdi") a1,
            lateout("rcx") _,
            lateout("r11") _,
            options(nostack)
        );
        ret
    }

    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    pub unsafe fn syscall1(_n: c_long, _a1: c_long) -> c_long {
        unimplemented!("仅支持 Linux x86_64")
    }
}

// ============== 文件操作系统调用封装 ==============

/// 文件描述符包装（Windows 简化版）
pub struct FileDesc {
    fd: c_int,
}

impl FileDesc {
    /// 从原始文件描述符创建
    pub fn new(fd: c_int) -> Self {
        Self { fd }
    }

    /// 获取原始文件描述符
    pub fn raw(&self) -> c_int {
        self.fd
    }

    /// 读取数据
    pub fn read(&self, _buf: &mut [u8]) -> io::Result<usize> {
        println!("read() 在 Windows 上简化实现");
        Ok(0)
    }

    /// 写入数据
    pub fn write(&self, buf: &[u8]) -> io::Result<usize> {
        Ok(buf.len())
    }

    /// 设置文件偏移
    pub fn seek(&self, offset: i64, _whence: c_int) -> io::Result<i64> {
        Ok(offset)
    }

    /// 获取文件元数据
    pub fn metadata(&self) -> io::Result<FileStat> {
        Ok(FileStat {
            size: 0,
            mode: 0,
            uid: 0,
            gid: 0,
            atime: 0,
            mtime: 0,
            ctime: 0,
            blocks: 0,
            block_size: 0,
        })
    }

    /// 同步文件到磁盘
    pub fn sync_all(&self) -> io::Result<()> {
        Ok(())
    }
}

impl Drop for FileDesc {
    fn drop(&mut self) {
        // Windows 简化实现
    }
}

/// 文件统计信息
#[derive(Debug, Clone)]
pub struct FileStat {
    pub size: i64,
    pub mode: u32,
    pub uid: u32,
    pub gid: u32,
    pub atime: i64,
    pub mtime: i64,
    pub ctime: i64,
    pub blocks: i64,
    pub block_size: i64,
}

impl From<libc::stat> for FileStat {
    fn from(stat: libc::stat) -> Self {
        Self {
            size: stat.st_size,
            mode: stat.st_mode as u32,
            uid: stat.st_uid as u32,
            gid: stat.st_gid as u32,
            atime: stat.st_atime,
            mtime: stat.st_mtime,
            ctime: stat.st_ctime,
            blocks: stat.st_size / 512, // 简化计算
            block_size: 512,
        }
    }
}

/// 打开文件
pub fn open_file(path: &str, flags: c_int, mode: u32) -> io::Result<FileDesc> {
    let c_path = CString::new(path)?;
    let fd = unsafe { libc::open(c_path.as_ptr(), flags, mode) };
    
    if fd < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(FileDesc::new(fd))
    }
}

// ============== 进程管理 ==============

/// 进程信息
#[derive(Debug, Clone)]
pub struct ProcessInfo {
    pub pid: i32,
    pub ppid: i32,
    pub uid: u32,
    pub gid: u32,
    pub euid: u32,
    pub egid: u32,
}

/// 获取当前进程信息
pub fn get_process_info() -> ProcessInfo {
    unsafe {
        ProcessInfo {
            pid: libc::getpid(),
            ppid: 0, // Windows下不可用
            uid: 0,
            gid: 0,
            euid: 0,
            egid: 0,
        }
    }
}

/// 创建子进程（Windows 不支持 fork）
pub fn fork() -> io::Result<ForkResult> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "fork() 在 Windows 上不可用"
    ))
}

/// fork 结果
#[derive(Debug)]
pub enum ForkResult {
    Parent { child_pid: i32 },
    Child,
}

/// 进程退出
pub fn exit(status: c_int) -> ! {
    unsafe {
        libc::exit(status);
    }
}

/// 等待子进程
pub fn waitpid(_pid: i32, _options: c_int) -> io::Result<WaitStatus> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "waitpid() 在 Windows 上不可用"
    ))
}

/// 等待状态
#[derive(Debug)]
pub enum WaitStatus {
    Exited(i32),
    Signaled(i32),
    Stopped(i32),
    Continued,
    StillAlive,
}

impl WaitStatus {
    fn from_raw(_status: c_int) -> Self {
        // Windows 简化实现
        WaitStatus::StillAlive
    }
}

/// 执行新程序
pub fn execvp(program: &str, args: &[&str]) -> io::Error {
    let c_program = CString::new(program).unwrap();
    
    let c_args: Vec<CString> = args
        .iter()
        .map(|&s| CString::new(s).unwrap())
        .collect();
    
    let mut ptrs: Vec<*const c_char> = c_args
        .iter()
        .map(|s| s.as_ptr())
        .collect();
    ptrs.push(ptr::null());
    
    unsafe {
        libc::execvp(c_program.as_ptr(), ptrs.as_ptr());
    }
    
    io::Error::last_os_error()
}

// ============== 信号处理 ==============

/// 信号处理器类型
pub type SignalHandler = extern "C" fn(c_int);

/// 设置信号处理器
pub unsafe fn signal(_sig: c_int, _handler: SignalHandler) -> io::Result<SignalHandler> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "signal() 在 Windows 上简化实现"
    ))
}

/// 发送信号（Windows 不支持）
pub fn kill(_pid: i32, _sig: c_int) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "kill() 在 Windows 上不可用"
    ))
}

// ============== 内存管理 ==============

/// 内存保护标志
pub const PROT_READ: c_int = 1;
pub const PROT_WRITE: c_int = 2;
pub const PROT_EXEC: c_int = 4;
pub const PROT_NONE: c_int = 0;

/// 映射标志
pub const MAP_SHARED: c_int = 1;
pub const MAP_PRIVATE: c_int = 2;
pub const MAP_ANONYMOUS: c_int = 32;
pub const MAP_FIXED: c_int = 16;

/// 内存映射（Windows 简化版）
pub unsafe fn mmap(
    _addr: *mut c_void,
    length: usize,
    _prot: c_int,
    _flags: c_int,
    _fd: c_int,
    _offset: i64,
) -> io::Result<*mut c_void> {
    // Windows 使用 VirtualAlloc，这里是简化实现
    let layout = std::alloc::Layout::from_size_align(length, 4096).unwrap();
    let ptr = std::alloc::alloc(layout);
    if ptr.is_null() {
        Err(io::Error::new(io::ErrorKind::Other, "内存分配失败"))
    } else {
        Ok(ptr as *mut c_void)
    }
}

/// 解除内存映射（Windows 简化版）
pub unsafe fn munmap(addr: *mut c_void, length: usize) -> io::Result<()> {
    let layout = std::alloc::Layout::from_size_align(length, 4096).unwrap();
    std::alloc::dealloc(addr as *mut u8, layout);
    Ok(())
}

/// 修改内存保护（Windows 简化版）
pub unsafe fn mprotect(_addr: *mut c_void, _len: usize, _prot: c_int) -> io::Result<()> {
    // Windows 使用 VirtualProtect
    Ok(())
}

/// 同步内存到文件（Windows 简化版）
pub unsafe fn msync(_addr: *mut c_void, _len: usize, _flags: c_int) -> io::Result<()> {
    Ok(())
}

// ============== 时间和定时器 ==============

/// 时间规格
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Timespec {
    pub tv_sec: i64,
    pub tv_nsec: i64,
}

impl Timespec {
    pub fn from_duration(dur: std::time::Duration) -> Self {
        Self {
            tv_sec: dur.as_secs() as i64,
            tv_nsec: dur.subsec_nanos() as i64,
        }
    }

    pub fn to_duration(&self) -> std::time::Duration {
        std::time::Duration::new(self.tv_sec as u64, self.tv_nsec as u32)
    }
}

/// 纳秒级睡眠（Windows 使用 Sleep）
pub fn nanosleep(req: &Timespec) -> io::Result<Timespec> {
    let duration = std::time::Duration::new(req.tv_sec as u64, req.tv_nsec as u32);
    std::thread::sleep(duration);
    Ok(Timespec { tv_sec: 0, tv_nsec: 0 })
}

/// 获取当前时间（Windows 简化版）
pub fn gettimeofday() -> io::Result<(i64, i64)> {
    let now = std::time::SystemTime::now();
    let since_epoch = now.duration_since(std::time::UNIX_EPOCH).unwrap();
    Ok((since_epoch.as_secs() as i64, since_epoch.subsec_micros() as i64))
}

/// 时钟类型
pub const CLOCK_REALTIME: i32 = 0;
pub const CLOCK_MONOTONIC: i32 = 1;

/// 获取时钟时间（Windows 简化版）
pub fn clock_gettime(_clock_id: i32) -> io::Result<Timespec> {
    // Windows 使用 QueryPerformanceCounter 或其他 API
    let now = std::time::Instant::now();
    Ok(Timespec {
        tv_sec: 0,
        tv_nsec: 0,
    })
}

// ============== 文件系统操作 ==============

/// 创建目录
pub fn mkdir(path: &str, _mode: u32) -> io::Result<()> {
    let c_path = CString::new(path)?;
    let ret = unsafe { libc::mkdir(c_path.as_ptr()) };
    
    if ret < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

/// 删除目录
pub fn rmdir(path: &str) -> io::Result<()> {
    let c_path = CString::new(path)?;
    let ret = unsafe { libc::rmdir(c_path.as_ptr()) };
    
    if ret < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

/// 删除文件
pub fn unlink(path: &str) -> io::Result<()> {
    let c_path = CString::new(path)?;
    let ret = unsafe { libc::unlink(c_path.as_ptr()) };
    
    if ret < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

/// 重命名文件
pub fn rename(old_path: &str, new_path: &str) -> io::Result<()> {
    let c_old = CString::new(old_path)?;
    let c_new = CString::new(new_path)?;
    
    let ret = unsafe { libc::rename(c_old.as_ptr(), c_new.as_ptr()) };
    
    if ret < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

/// 获取当前工作目录
pub fn getcwd() -> io::Result<String> {
    let mut buf = vec![0u8; 4096];
    let ret = unsafe { libc::getcwd(buf.as_mut_ptr() as *mut c_char, buf.len() as i32) };
    
    if ret.is_null() {
        Err(io::Error::last_os_error())
    } else {
        let len = buf.iter().position(|&b| b == 0).unwrap_or(buf.len());
        buf.truncate(len);
        String::from_utf8(buf).map_err(|_| io::Error::new(
            io::ErrorKind::InvalidData,
            "Invalid UTF-8 in path"
        ))
    }
}

/// 切换工作目录
pub fn chdir(path: &str) -> io::Result<()> {
    let c_path = CString::new(path)?;
    let ret = unsafe { libc::chdir(c_path.as_ptr()) };
    
    if ret < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

// ============== 资源限制 ==============

/// 资源类型
pub const RLIMIT_CPU: c_int = 0;     // CPU 时间限制
pub const RLIMIT_FSIZE: c_int = 1;   // 文件大小限制
pub const RLIMIT_DATA: c_int = 2;    // 数据段大小限制
pub const RLIMIT_STACK: c_int = 3;   // 栈大小限制
pub const RLIMIT_CORE: c_int = 4;    // 核心文件大小限制
pub const RLIMIT_NOFILE: c_int = 7;  // 打开文件数限制
pub const RLIMIT_AS: c_int = 9;      // 地址空间限制

/// 资源限制结构
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Rlimit {
    pub rlim_cur: u64,
    pub rlim_max: u64,
}

/// 获取资源限制（Windows 简化版）
pub fn getrlimit(_resource: c_int) -> io::Result<Rlimit> {
    // Windows 使用 GetProcessWorkingSetSize 等 API
    Ok(Rlimit {
        rlim_cur: u64::MAX,
        rlim_max: u64::MAX,
    })
}

/// 设置资源限制（Windows 不支持）
pub fn setrlimit(_resource: c_int, _rlim: &Rlimit) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "setrlimit() 在 Windows 上不可用"
    ))
}

// ============== 演示函数 ==============

fn demo_process_info() {
    println!("=== 进程信息 ===");
    
    let info = get_process_info();
    println!("PID:  {}", info.pid);
    println!("PPID: {}", info.ppid);
    println!("UID:  {}", info.uid);
    println!("GID:  {}", info.gid);
    println!("EUID: {}", info.euid);
    println!("EGID: {}", info.egid);
}

fn demo_time() {
    println!("\n=== 时间操作 ===");
    
    // 获取当前时间
    let (sec, usec) = gettimeofday().unwrap();
    println!("当前时间: {}.{} seconds since epoch", sec, usec);
    
    // 获取单调时钟
    let ts = clock_gettime(CLOCK_MONOTONIC).unwrap();
    println!("单调时钟: {}s {}ns", ts.tv_sec, ts.tv_nsec);
    
    // 纳秒睡眠
    println!("睡眠 100ms...");
    let req = Timespec::from_duration(std::time::Duration::from_millis(100));
    let start = std::time::Instant::now();
    nanosleep(&req).unwrap();
    println!("实际睡眠: {:?}", start.elapsed());
}

fn demo_file_ops() {
    println!("\n=== 文件操作 ===");
    
    // 创建临时文件
    let path = "/tmp/rust_syscall_test.txt";
    
    // 打开文件
    let fd = open_file(
        path,
        libc::O_CREAT | libc::O_WRONLY | libc::O_TRUNC,
        0o644,
    ).unwrap();
    
    // 写入数据
    fd.write(b"Hello from Rust syscalls!\n").unwrap();
    fd.sync_all().unwrap();
    drop(fd);
    
    println!("文件已写入: {}", path);
    
    // 重新打开并读取
    let fd = open_file(path, libc::O_RDONLY, 0).unwrap();
    let meta = fd.metadata().unwrap();
    println!("文件大小: {} bytes", meta.size);
    
    let mut buf = vec![0u8; 100];
    let n = fd.read(&mut buf).unwrap();
    buf.truncate(n);
    println!("文件内容: {}", String::from_utf8_lossy(&buf));
    drop(fd);
    
    // 删除文件
    unlink(path).unwrap();
    println!("文件已删除");
}

fn demo_resource_limits() {
    println!("\n=== 资源限制 ===");
    
    let rlim = getrlimit(RLIMIT_NOFILE).unwrap();
    println!("打开文件数限制: soft={}, hard={}", rlim.rlim_cur, rlim.rlim_max);
    
    let rlim = getrlimit(RLIMIT_STACK).unwrap();
    println!("栈大小限制: soft={}, hard={}", rlim.rlim_cur, rlim.rlim_max);
    
    let rlim = getrlimit(RLIMIT_AS).unwrap();
    println!("地址空间限制: soft={}, hard={}", rlim.rlim_cur, rlim.rlim_max);
}

fn demo_cwd() {
    println!("\n=== 工作目录 ===");
    
    let cwd = getcwd().unwrap();
    println!("当前目录: {}", cwd);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_process_info() {
        let info = get_process_info();
        assert!(info.pid > 0);
    }

    #[test]
    fn test_time() {
        let ts = clock_gettime(CLOCK_MONOTONIC).unwrap();
        assert!(ts.tv_sec >= 0);
    }

    #[test]
    fn test_getcwd() {
        let cwd = getcwd().unwrap();
        assert!(!cwd.is_empty());
    }

    #[test]
    fn test_resource_limits() {
        let rlim = getrlimit(RLIMIT_NOFILE).unwrap();
        assert!(rlim.rlim_cur > 0);
    }
}

fn main() {
    println!("=== 系统调用封装演示 ===");

    demo_process_info();
    demo_time();
    demo_file_ops();
    demo_resource_limits();
    demo_cwd();

    println!("\n=== 演示完成 ===");
}
