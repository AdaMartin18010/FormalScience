//! AST (Abstract Syntax Tree) 定义
//! 
//! 定义类型检查器支持的表达式、类型和声明的抽象语法树。

use std::collections::HashMap;
use std::fmt;

/// 程序由多个声明组成
pub type Program = Vec<Decl>;

/// 声明类型
#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    /// 变量声明: let name: Type = expr
    Let {
        name: String,
        ty: Option<Type>, // 可选的类型注解
        value: Expr,
    },
    /// 函数声明: fn name<T>(params) -> ret_type { body }
    Fun {
        name: String,
        generics: Vec<String>,
        params: Vec<(String, Type)>,
        ret_type: Type,
        body: Expr,
    },
    /// 类型别名: type Name = Type
    TypeAlias {
        name: String,
        ty: Type,
    },
}

/// 表达式类型
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// 整数常量
    Int(i64),
    /// 布尔常量
    Bool(bool),
    /// 字符串常量
    String(String),
    /// 单位值
    Unit,
    
    /// 变量引用
    Var(String),
    
    /// 二元运算
    BinOp {
        op: BinOperator,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    
    /// 一元运算
    UnOp {
        op: UnOperator,
        operand: Box<Expr>,
    },
    
    /// 条件表达式: if cond then else
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },
    
    /// 代码块: { expr1; expr2; ...; exprN }
    Block(Vec<Expr>),
    
    /// 函数调用
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    
    /// 记录构造: { field1 = expr1, field2 = expr2 }
    Record(HashMap<String, Expr>),
    
    /// 字段访问: expr.field
    FieldAccess {
        expr: Box<Expr>,
        field: String,
    },
    
    /// 数组构造: [expr1, expr2, ...]
    Array(Vec<Expr>),
    
    /// 数组索引: expr[index]
    Index {
        expr: Box<Expr>,
        index: Box<Expr>,
    },
    
    /// 类型注解: expr : Type
    Annotated {
        expr: Box<Expr>,
        ty: Type,
    },
}

/// 二元运算符
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOperator {
    // 算术
    Add,    // +
    Sub,    // -
    Mul,    // *
    Div,    // /
    Mod,    // %
    
    // 比较
    Eq,     // ==
    Ne,     // !=
    Lt,     // <
    Le,     // <=
    Gt,     // >
    Ge,     // >=
    
    // 逻辑
    And,    // &&
    Or,     // ||
}

impl fmt::Display for BinOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOperator::Add => write!(f, "+"),
            BinOperator::Sub => write!(f, "-"),
            BinOperator::Mul => write!(f, "*"),
            BinOperator::Div => write!(f, "/"),
            BinOperator::Mod => write!(f, "%"),
            BinOperator::Eq => write!(f, "=="),
            BinOperator::Ne => write!(f, "!="),
            BinOperator::Lt => write!(f, "<"),
            BinOperator::Le => write!(f, "<="),
            BinOperator::Gt => write!(f, ">"),
            BinOperator::Ge => write!(f, ">="),
            BinOperator::And => write!(f, "&&"),
            BinOperator::Or => write!(f, "||"),
        }
    }
}

/// 一元运算符
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOperator {
    Neg,    // -
    Not,    // !
}

impl fmt::Display for UnOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnOperator::Neg => write!(f, "-"),
            UnOperator::Not => write!(f, "!"),
        }
    }
}

/// 类型定义
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// 整数类型
    Int,
    /// 布尔类型
    Bool,
    /// 字符串类型
    String,
    /// 单位类型
    Unit,
    
    /// 类型变量（用于泛型和类型推断）
    Var(String),
    
    /// 函数类型: ArgType -> RetType
    Fun {
        params: Vec<Type>,
        ret: Box<Type>,
    },
    
    /// 数组类型: [Type]
    Array(Box<Type>),
    
    /// 元组类型: (Type1, Type2, ...)
    Tuple(Vec<Type>),
    
    /// 记录类型: { field1: Type1, field2: Type2 }
    Record(HashMap<String, Type>),
    
    /// 变体类型（枚举）: Variant1 | Variant2 | ...
    Variant(Vec<(String, Option<Type>)>),
    
    /// 泛型类型: Type<T1, T2, ...>
    Generic {
        base: Box<Type>,
        args: Vec<Type>,
    },
}

impl Type {
    /// 检查是否为基础类型
    pub fn is_primitive(&self) -> bool {
        matches!(self, Type::Int | Type::Bool | Type::String | Type::Unit)
    }

    /// 检查是否为函数类型
    pub fn is_function(&self) -> bool {
        matches!(self, Type::Fun { .. })
    }

    /// 创建函数类型的便捷方法
    pub fn fun(params: Vec<Type>, ret: Type) -> Self {
        Type::Fun {
            params,
            ret: Box::new(ret),
        }
    }

    /// 创建数组类型的便捷方法
    pub fn array(elem: Type) -> Self {
        Type::Array(Box::new(elem))
    }

    /// 创建元组类型的便捷方法
    pub fn tuple(types: Vec<Type>) -> Self {
        Type::Tuple(types)
    }

    /// 获取类型的字符串表示（简化版）
    pub fn name(&self) -> String {
        format!("{}", self)
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::String => write!(f, "String"),
            Type::Unit => write!(f, "Unit"),
            Type::Var(name) => write!(f, "{}", name),
            Type::Fun { params, ret } => {
                write!(f, "(")?;
                for (i, param) in params.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", param)?;
                }
                write!(f, ") -> {}", ret)
            }
            Type::Array(elem) => write!(f, "[{}]", elem),
            Type::Tuple(types) => {
                write!(f, "(")?;
                for (i, ty) in types.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", ty)?;
                }
                write!(f, ")")
            }
            Type::Record(fields) => {
                write!(f, "{{ ")?;
                for (i, (name, ty)) in fields.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}: {}", name, ty)?;
                }
                write!(f, " }}")
            }
            Type::Variant(variants) => {
                for (i, (name, ty)) in variants.iter().enumerate() {
                    if i > 0 { write!(f, " | ")?; }
                    match ty {
                        Some(t) => write!(f, "{}({})", name, t)?,
                        None => write!(f, "{}", name)?,
                    }
                }
                Ok(())
            }
            Type::Generic { base, args } => {
                write!(f, "{}", base)?;
                write!(f, "<")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", arg)?;
                }
                write!(f, ">")
            }
        }
    }
}

/// 位置信息（用于错误报告）
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// 带位置信息的 AST 节点
#[derive(Debug, Clone, PartialEq)]
pub struct Located<T> {
    pub node: T,
    pub pos: Position,
}

impl<T> Located<T> {
    pub fn new(node: T, line: usize, column: usize) -> Self {
        Located {
            node,
            pos: Position { line, column },
        }
    }
}

/// 创建 AST 的辅助函数
pub mod utils {
    use super::*;

    /// 创建整数表达式
    pub fn int(n: i64) -> Expr {
        Expr::Int(n)
    }

    /// 创建布尔表达式
    pub fn bool(b: bool) -> Expr {
        Expr::Bool(b)
    }

    /// 创建字符串表达式
    pub fn string(s: &str) -> Expr {
        Expr::String(s.to_string())
    }

    /// 创建变量表达式
    pub fn var(name: &str) -> Expr {
        Expr::Var(name.to_string())
    }

    /// 创建二元运算
    pub fn binop(op: BinOperator, left: Expr, right: Expr) -> Expr {
        Expr::BinOp {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// 创建函数调用
    pub fn call(func: Expr, args: Vec<Expr>) -> Expr {
        Expr::Call {
            func: Box::new(func),
            args,
        }
    }

    /// 创建 let 声明
    pub fn let_decl(name: &str, value: Expr) -> Decl {
        Decl::Let {
            name: name.to_string(),
            ty: None,
            value,
        }
    }

    /// 创建带类型的 let 声明
    pub fn let_decl_typed(name: &str, ty: Type, value: Expr) -> Decl {
        Decl::Let {
            name: name.to_string(),
            ty: Some(ty),
            value,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::utils::*;

    #[test]
    fn test_type_display() {
        assert_eq!(format!("{}", Type::Int), "Int");
        assert_eq!(format!("{}", Type::Bool), "Bool");
        assert_eq!(format!("{}", Type::array(Type::Int)), "[Int]");
        
        let fun_type = Type::fun(vec![Type::Int, Type::Int], Type::Bool);
        assert_eq!(format!("{}", fun_type), "(Int, Int) -> Bool");
    }

    #[test]
    fn test_expr_construction() {
        let expr = binop(BinOperator::Add, int(1), int(2));
        assert!(matches!(expr, Expr::BinOp { .. }));
    }

    #[test]
    fn test_record_type() {
        let mut fields = HashMap::new();
        fields.insert("x".to_string(), Type::Int);
        fields.insert("y".to_string(), Type::Int);
        let record = Type::Record(fields);
        
        assert!(matches!(record, Type::Record(_)));
    }
}
