//! # 类型级编程
//! 
//! 展示 Rust 的类型级编程能力，包括：
//! - 类型级数值
//! - Phantom Types
//! - 状态机类型
//! - 类型级列表

use std::marker::PhantomData;

// ==================== 类型级布尔 ====================

/// 类型级真值
pub struct True;
/// 类型级假值
pub struct False;

/// 类型级布尔运算 trait
pub trait Bool {
    type Not: Bool;
    type And<B: Bool>: Bool;
    type Or<B: Bool>: Bool;
    const VALUE: bool;
}

impl Bool for True {
    type Not = False;
    type And<B: Bool> = B;
    type Or<B: Bool> = True;
    const VALUE: bool = true;
}

impl Bool for False {
    type Not = True;
    type And<B: Bool> = False;
    type Or<B: Bool> = B;
    const VALUE: bool = false;
}

// ==================== 类型级自然数 ====================

/// 零类型
pub struct Z;
/// 后继类型
pub struct S<N>(PhantomData<N>);

/// 类型级自然数 trait
pub trait Nat {
    const VALUE: usize;
    type Add<M: Nat>: Nat;
    type Mul<M: Nat>: Nat;
    type Eq<M: Nat>: Bool;
    type Lt<M: Nat>: Bool;
}

impl Nat for Z {
    const VALUE: usize = 0;
    type Add<M: Nat> = M;
    type Mul<M: Nat> = Z;
    type Eq<M: Nat> = <M as Nat>::IsZero;
    type Lt<M: Nat> = <M as Nat>::IsNonZero;
}

impl<N: Nat> Nat for S<N> {
    const VALUE: usize = 1 + N::VALUE;
    type Add<M: Nat> = S<<N as Nat>::Add<M>>;
    type Mul<M: Nat> = <M as Nat>::Add<<N as Nat>::Mul<M>>;
    type Eq<M: Nat> = <M as Nat>::EqSucc<N>;
    type Lt<M: Nat> = <M as Nat>::GtSucc<N>;
}

// 辅助 trait
pub trait NatExt: Nat {
    type IsZero: Bool;
    type IsNonZero: Bool;
    type EqSucc<M: Nat>: Bool;
    type GtSucc<M: Nat>: Bool;
}

impl NatExt for Z {
    type IsZero = True;
    type IsNonZero = False;
    type EqSucc<M: Nat> = False;
    type GtSucc<M: Nat> = False;
}

impl<N: Nat> NatExt for S<N> {
    type IsZero = False;
    type IsNonZero = True;
    type EqSucc<M: Nat> = <M as NatExt>::Eq<N>;
    type GtSucc<M: Nat> = <M as NatExt>::Eq<N>;
}

// ==================== Phantom Types 状态机 ====================

/// 未初始化状态
pub struct Uninitialized;
/// 已初始化状态
pub struct Initialized;
/// 运行中状态
pub struct Running;
/// 已停止状态
pub struct Stopped;

/// 状态机：使用 Phantom Types 在编译时保证状态转换的正确性
pub struct StateMachine<State> {
    data: String,
    _state: PhantomData<State>,
}

impl StateMachine<Uninitialized> {
    pub fn new() -> Self {
        Self {
            data: String::new(),
            _state: PhantomData,
        }
    }
    
    pub fn init(self, config: impl Into<String>) -> StateMachine<Initialized> {
        StateMachine {
            data: config.into(),
            _state: PhantomData,
        }
    }
}

impl StateMachine<Initialized> {
    pub fn start(self) -> StateMachine<Running> {
        StateMachine {
            data: self.data,
            _state: PhantomData,
        }
    }
    
    pub fn get_config(&self) -> &str {
        &self.data
    }
}

impl StateMachine<Running> {
    pub fn process(&mut self, input: impl AsRef<str>) -> String {
        format!("Processing '{}' with config '{}'", input.as_ref(), self.data)
    }
    
    pub fn stop(self) -> StateMachine<Stopped> {
        StateMachine {
            data: self.data,
            _state: PhantomData,
        }
    }
}

impl StateMachine<Stopped> {
    pub fn reset(self) -> StateMachine<Uninitialized> {
        StateMachine::new()
    }
    
    pub fn get_data(&self) -> &str {
        &self.data
    }
}

// ==================== 类型级列表 ====================

/// 空列表
pub struct Nil;
/// 列表构造
pub struct Cons<H, T>(PhantomData<(H, T)>);

/// 类型级列表操作
pub trait List {
    type Len: Nat;
    type Head;
    type Tail: List;
    type Append<L: List>: List;
    type Reverse: List;
}

impl List for Nil {
    type Len = Z;
    type Head = ();
    type Tail = Nil;
    type Append<L: List> = L;
    type Reverse = Nil;
}

impl<H, T: List> List for Cons<H, T> {
    type Len = S<T::Len>;
    type Head = H;
    type Tail = T;
    type Append<L: List> = Cons<H, T::Append<L>>;
    type Reverse = <Self::ReverseAcc<Nil> as List>::Reverse;
}

pub trait ReverseAcc<A: List>: List {
    type ReverseAcc: List;
}

impl<A: List> ReverseAcc<A> for Nil {
    type ReverseAcc = A;
}

impl<H, T: List, A: List> ReverseAcc<A> for Cons<H, T> {
    type ReverseAcc = T::ReverseAcc<Cons<H, A>>;
}

// ==================== 维度类型 ====================

/// 米
pub struct Meter;
/// 秒
pub struct Second;
/// 千克
pub struct Kilogram;

/// 带维度标记的数值
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Dimensioned<T, D>(T, PhantomData<D>);

impl<T, D> Dimensioned<T, D> {
    pub fn new(value: T) -> Self {
        Self(value, PhantomData)
    }
    
    pub fn value(&self) -> &T {
        &self.0
    }
    
    pub fn into_inner(self) -> T {
        self.0
    }
}

use std::ops::{Add, Sub, Mul, Div};

/// 维度乘法结果
pub struct DimMul<D1, D2>(PhantomData<(D1, D2)>);
/// 维度除法结果
pub struct DimDiv<D1, D2>(PhantomData<(D1, D2)>);

impl<T: Add<Output = T>, D> Add for Dimensioned<T, D> {
    type Output = Self;
    
    fn add(self, other: Self) -> Self {
        Self::new(self.0 + other.0)
    }
}

impl<T: Sub<Output = T>, D> Sub for Dimensioned<T, D> {
    type Output = Self;
    
    fn sub(self, other: Self) -> Self {
        Self::new(self.0 - other.0)
    }
}

impl<T: Mul<Output = T>, D1, D2> Mul<Dimensioned<T, D2>> for Dimensioned<T, D1> {
    type Output = Dimensioned<T, DimMul<D1, D2>>;
    
    fn mul(self, other: Dimensioned<T, D2>) -> Self::Output {
        Dimensioned::new(self.0 * other.0)
    }
}

impl<T: Div<Output = T>, D1, D2> Div<Dimensioned<T, D2>> for Dimensioned<T, D1> {
    type Output = Dimensioned<T, DimDiv<D1, D2>>;
    
    fn div(self, other: Dimensioned<T, D2>) -> Self::Output {
        Dimensioned::new(self.0 / other.0)
    }
}

/// 类型别名方便使用
pub type Length<T> = Dimensioned<T, Meter>;
pub type Time<T> = Dimensioned<T, Second>;
pub type Mass<T> = Dimensioned<T, Kilogram>;
pub type Velocity<T> = Dimensioned<T, DimDiv<Meter, Second>>;

// ==================== 编译期验证的邮箱 ====================

/// 验证过的邮箱
#[derive(Debug, Clone, PartialEq)]
pub struct ValidatedEmail(String);

/// 未验证的邮箱
#[derive(Debug, Clone, PartialEq)]
pub struct UnvalidatedEmail(String);

impl UnvalidatedEmail {
    pub fn new(email: impl Into<String>) -> Self {
        Self(email.into())
    }
    
    pub fn validate(self) -> Result<ValidatedEmail, EmailError> {
        let email = self.0;
        if email.contains('@') && email.contains('.') {
            Ok(ValidatedEmail(email))
        } else {
            Err(EmailError::InvalidFormat)
        }
    }
}

impl ValidatedEmail {
    pub fn as_str(&self) -> &str {
        &self.0
    }
    
    pub fn domain(&self) -> &str {
        self.0.split('@').nth(1).unwrap_or("")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum EmailError {
    InvalidFormat,
}

/// 类型级别的权限系统
pub struct Read;
pub struct Write;
pub struct Execute;

pub struct Permissions<R, W, X>(PhantomData<(R, W, X)>);

pub type ReadOnly = Permissions<True, False, False>;
pub type WriteOnly = Permissions<False, True, False>;
pub type ReadWrite = Permissions<True, True, False>;
pub type FullAccess = Permissions<True, True, True>;

pub struct FileHandle<P>(String, PhantomData<P>);

impl FileHandle<ReadOnly> {
    pub fn open_read(path: impl Into<String>) -> Self {
        Self(path.into(), PhantomData)
    }
    
    pub fn read(&self) -> String {
        format!("Reading from {}", self.0)
    }
}

impl FileHandle<ReadWrite> {
    pub fn open_write(path: impl Into<String>) -> Self {
        Self(path.into(), PhantomData)
    }
    
    pub fn write(&mut self, content: impl AsRef<str>) {
        println!("Writing '{}' to {}", content.as_ref(), self.0);
    }
    
    pub fn read(&self) -> String {
        format!("Reading from {}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_level_bool() {
        assert!(<True as Bool>::VALUE);
        assert!(!<False as Bool>::VALUE);
        
        // True && False == False
        assert!(!<<True as Bool>::And<False> as Bool>::VALUE);
        // True || False == True
        assert!(<<True as Bool>::Or<False> as Bool>::VALUE);
    }

    #[test]
    fn test_type_level_nat() {
        // 类型级 2
        type Two = S<S<Z>>;
        assert_eq!(<Two as Nat>::VALUE, 2);
        
        // 2 + 1 = 3
        type Three = <Two as Nat>::Add<S<Z>>;
        assert_eq!(<Three as Nat>::VALUE, 3);
    }

    #[test]
    fn test_state_machine() {
        let sm = StateMachine::new();
        let sm = sm.init("config data");
        assert_eq!(sm.get_config(), "config data");
        
        let mut sm = sm.start();
        let result = sm.process("input");
        assert!(result.contains("Processing"));
        
        let sm = sm.stop();
        assert_eq!(sm.get_data(), "config data");
    }

    #[test]
    fn test_dimensioned() {
        let length1: Length<f64> = Dimensioned::new(10.0);
        let length2: Length<f64> = Dimensioned::new(5.0);
        let sum = length1 + length2;
        assert_eq!(*sum.value(), 15.0);
        
        let time: Time<f64> = Dimensioned::new(2.0);
        let velocity = sum / time;
        assert_eq!(*velocity.value(), 7.5);
    }

    #[test]
    fn test_email_validation() {
        let unvalidated = UnvalidatedEmail::new("test@example.com");
        let validated = unvalidated.validate().unwrap();
        assert_eq!(validated.domain(), "example.com");
        
        let invalid = UnvalidatedEmail::new("invalid-email");
        assert!(invalid.validate().is_err());
    }

    #[test]
    fn test_file_permissions() {
        let file = FileHandle::<ReadOnly>::open_read("test.txt");
        assert_eq!(file.read(), "Reading from test.txt");
        
        let mut rw_file = FileHandle::<ReadWrite>::open_write("test.txt");
        rw_file.write("Hello");
        assert_eq!(rw_file.read(), "Reading from test.txt");
    }
}
