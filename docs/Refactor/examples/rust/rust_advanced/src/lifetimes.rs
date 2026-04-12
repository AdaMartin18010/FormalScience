//! # 生命周期高级特性
//! 
//! 展示 Rust 生命周期的深入概念，包括：
//! - 显式生命周期标注
//! - 生命周期省略规则
//! - 生命周期边界
//! - 自引用结构

use std::marker::PhantomData;

/// 字符串切片迭代器
pub struct StrSplitter<'a> {
    text: &'a str,
    delimiter: char,
    position: usize,
}

impl<'a> StrSplitter<'a> {
    pub fn new(text: &'a str, delimiter: char) -> Self {
        Self {
            text,
            delimiter,
            position: 0,
        }
    }
}

impl<'a> Iterator for StrSplitter<'a> {
    type Item = &'a str;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.position >= self.text.len() {
            return None;
        }
        
        let remaining = &self.text[self.position..];
        match remaining.find(self.delimiter) {
            Some(idx) => {
                let result = &remaining[..idx];
                self.position += idx + 1;
                Some(result)
            }
            None => {
                self.position = self.text.len();
                Some(remaining)
            }
        }
    }
}

/// 泛型生命周期示例
pub fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

/// 多重生命周期
pub fn extract_between<'a, 'b>(
    text: &'a str,
    start: &'b str,
    end: &'b str,
) -> Option<&'a str> {
    let start_idx = text.find(start)? + start.len();
    let end_idx = text[start_idx..].find(end)?;
    Some(&text[start_idx..start_idx + end_idx])
}

/// 带有生命周期的结构体
pub struct BorrowedData<'a, T> {
    data: &'a T,
    name: String,
}

impl<'a, T> BorrowedData<'a, T> {
    pub fn new(data: &'a T, name: impl Into<String>) -> Self {
        Self {
            data,
            name: name.into(),
        }
    }
    
    pub fn get(&self) -> &'a T {
        self.data
    }
    
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// 生命周期边界：确保引用在特定范围内有效
pub trait LendingIterator {
    type Item<'a>
    where
        Self: 'a;
    
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

///  arenas 模式：所有分配具有相同生命周期
pub struct Arena<'a, T> {
    data: Vec<T>,
    _phantom: PhantomData<&'a ()>,
}

impl<'a, T> Arena<'a, T> {
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            _phantom: PhantomData,
        }
    }
    
    pub fn alloc(&mut self, value: T) -> &'a T {
        self.data.push(value);
        // 这种用法不安全，仅用于演示概念
        // 实际实现需要更复杂的内存管理
        unsafe { &*(self.data.last().unwrap() as *const T) }
    }
    
    pub fn len(&self) -> usize {
        self.data.len()
    }
    
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

impl<'a, T> Default for Arena<'a, T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 作用域守卫：确保资源在作用域结束时释放
pub struct ScopeGuard<F: FnOnce()> {
    f: Option<F>,
}

impl<F: FnOnce()> ScopeGuard<F> {
    pub fn new(f: F) -> Self {
        Self { f: Some(f) }
    }
    
    pub fn dismiss(mut self) {
        self.f.take();
    }
}

impl<F: FnOnce()> Drop for ScopeGuard<F> {
    fn drop(&mut self) {
        if let Some(f) = self.f.take() {
            f();
        }
    }
}

/// 自引用结构的安全包装
pub struct SelfReferential<T, F> {
    data: T,
    // 使用函数指针避免生命周期问题
    extractor: F,
}

impl<T, F, R> SelfReferential<T, F>
where
    F: Fn(&T) -> &R,
{
    pub fn new(data: T, extractor: F) -> Self {
        Self { data, extractor }
    }
    
    pub fn get(&self) -> &R {
        (self.extractor)(&self.data)
    }
    
    pub fn into_inner(self) -> T {
        self.data
    }
}

/// 使用 Pin 的自引用结构
pub use std::pin::Pin;

/// 字符串解析器：持有对输入的引用
pub struct Parser<'input> {
    input: &'input str,
    position: usize,
}

impl<'input> Parser<'input> {
    pub fn new(input: &'input str) -> Self {
        Self { input, position: 0 }
    }
    
    pub fn peek(&self) -> Option<char> {
        self.input[self.position..].chars().next()
    }
    
    pub fn consume(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.position += ch.len_utf8();
        Some(ch)
    }
    
    pub fn parse_while<F>(&mut self, predicate: F) -> &'input str
    where
        F: Fn(char) -> bool,
    {
        let start = self.position;
        while let Some(ch) = self.peek() {
            if !predicate(ch) {
                break;
            }
            self.consume();
        }
        &self.input[start..self.position]
    }
    
    pub fn parse_number(&mut self) -> Option<i64> {
        let num_str = self.parse_while(|c| c.is_ascii_digit());
        if num_str.is_empty() {
            None
        } else {
            num_str.parse().ok()
        }
    }
}

/// 生命周期子类型关系
pub fn borrow_as<'short, 'long: 'short>(x: &'long str) -> &'short str {
    x
}

/// 静态生命周期
pub fn get_static_string() -> &'static str {
    "This string lives for the entire program duration"
}

/// 生命周期与 trait 对象
pub trait ParserTrait<'input> {
    fn parse(&mut self) -> Option<&'input str>;
}

impl<'input> ParserTrait<'input> for Parser<'input> {
    fn parse(&mut self) -> Option<&'input str> {
        self.parse_while(|c| !c.is_whitespace()).into()
    }
}

/// 编译期计算字符串长度
pub const fn const_strlen(s: &str) -> usize {
    s.len()
}

/// 数组视图：安全的切片包装
pub struct ArrayView<'a, T> {
    slice: &'a [T],
    start: usize,
    end: usize,
}

impl<'a, T> ArrayView<'a, T> {
    pub fn new(slice: &'a [T]) -> Self {
        let len = slice.len();
        Self {
            slice,
            start: 0,
            end: len,
        }
    }
    
    pub fn slice(&self, start: usize, end: usize) -> Option<Self> {
        if start > end || self.start + end > self.end {
            return None;
        }
        Some(Self {
            slice: self.slice,
            start: self.start + start,
            end: self.start + end,
        })
    }
    
    pub fn get(&self, index: usize) -> Option<&'a T> {
        if self.start + index >= self.end {
            return None;
        }
        Some(&self.slice[self.start + index])
    }
    
    pub fn len(&self) -> usize {
        self.end - self.start
    }
    
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, T> IntoIterator for ArrayView<'a, T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    
    fn into_iter(self) -> Self::IntoIter {
        self.slice[self.start..self.end].iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_str_splitter() {
        let text = "hello,world,foo,bar";
        let splitter = StrSplitter::new(text, ',');
        let parts: Vec<_> = splitter.collect();
        assert_eq!(parts, vec!["hello", "world", "foo", "bar"]);
    }

    #[test]
    fn test_longest() {
        let s1 = "short";
        let s2 = "longer string";
        assert_eq!(longest(s1, s2), s2);
    }

    #[test]
    fn test_extract_between() {
        let text = "Hello [world] there";
        assert_eq!(extract_between(text, "[", "]"), Some("world"));
    }

    #[test]
    fn test_borrowed_data() {
        let value = 42;
        let borrowed = BorrowedData::new(&value, "test");
        assert_eq!(*borrowed.get(), 42);
        assert_eq!(borrowed.name(), "test");
    }

    #[test]
    fn test_parser() {
        let mut parser = Parser::new("123abc");
        assert_eq!(parser.parse_number(), Some(123));
        assert_eq!(parser.parse_while(|c| c.is_ascii_alphabetic()), "abc");
    }

    #[test]
    fn test_scope_guard() {
        let mut flag = false;
        {
            let _guard = ScopeGuard::new(|| flag = true);
        }
        assert!(flag);
    }

    #[test]
    fn test_array_view() {
        let data = vec![1, 2, 3, 4, 5];
        let view = ArrayView::new(&data);
        let subview = view.slice(1, 4).unwrap();
        
        assert_eq!(subview.get(0), Some(&2));
        assert_eq!(subview.get(2), Some(&4));
        assert_eq!(subview.len(), 3);
    }

    #[test]
    fn test_self_referential() {
        let data = vec![1, 2, 3, 4, 5];
        let wrapper = SelfReferential::new(data, |v: &Vec<i32>| &v[2]);
        assert_eq!(*wrapper.get(), 3);
    }
}
