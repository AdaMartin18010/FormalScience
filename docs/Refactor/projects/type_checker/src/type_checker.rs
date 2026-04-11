//! 类型检查器实现
//! 
//! 实现 Hindley-Milner 风格的类型推断和检查。

use crate::ast::*;
use std::collections::HashMap;

/// 类型错误
#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    /// 类型不匹配
    TypeMismatch { expected: Type, found: Type, pos: Position },
    /// 未定义的变量
    UndefinedVar { name: String, pos: Position },
    /// 未定义的函数
    UndefinedFun { name: String, pos: Position },
    /// 参数数量不匹配
    ArgCountMismatch { expected: usize, found: usize, pos: Position },
    /// 未定义的类型
    UndefinedType { name: String, pos: Position },
    /// 无限类型（递归类型）
    InfiniteType { ty_var: String, ty: Type, pos: Position },
    /// 泛型参数数量不匹配
    GenericArgCountMismatch { expected: usize, found: usize, pos: Position },
    /// 二元运算符类型错误
    InvalidBinOp { op: BinOperator, left: Type, right: Type, pos: Position },
    /// 一元运算符类型错误
    InvalidUnOp { op: UnOperator, operand: Type, pos: Position },
    /// 条件分支类型不匹配
    BranchTypeMismatch { then_type: Type, else_type: Type, pos: Position },
    /// 不可调用的类型
    NotCallable { ty: Type, pos: Position },
    /// 字段不存在
    FieldNotFound { field: String, ty: Type, pos: Position },
    /// 记录缺少字段
    MissingFields { fields: Vec<String>, ty: Type, pos: Position },
    /// 无效的语法
    InvalidSyntax { message: String, pos: Position },
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TypeError::*;
        match self {
            TypeMismatch { expected, found, pos } => {
                write!(f, "Type error at {}: expected '{}', found '{}'", 
                    pos, expected, found)
            }
            UndefinedVar { name, pos } => {
                write!(f, "Type error at {}: undefined variable '{}'", pos, name)
            }
            UndefinedFun { name, pos } => {
                write!(f, "Type error at {}: undefined function '{}'", pos, name)
            }
            ArgCountMismatch { expected, found, pos } => {
                write!(f, "Type error at {}: function expects {} arguments, found {}", 
                    pos, expected, found)
            }
            UndefinedType { name, pos } => {
                write!(f, "Type error at {}: undefined type '{}'", pos, name)
            }
            InfiniteType { ty_var, ty, pos } => {
                write!(f, "Type error at {}: infinite type detected: {} = {}", 
                    pos, ty_var, ty)
            }
            InvalidBinOp { op, left, right, pos } => {
                write!(f, "Type error at {}: cannot apply '{}' to '{}' and '{}'", 
                    pos, op, left, right)
            }
            InvalidUnOp { op, operand, pos } => {
                write!(f, "Type error at {}: cannot apply '{}' to '{}'", 
                    pos, op, operand)
            }
            BranchTypeMismatch { then_type, else_type, pos } => {
                write!(f, "Type error at {}: branch type mismatch: '{}' and '{}'", 
                    pos, then_type, else_type)
            }
            NotCallable { ty, pos } => {
                write!(f, "Type error at {}: type '{}' is not callable", pos, ty)
            }
            FieldNotFound { field, ty, pos } => {
                write!(f, "Type error at {}: field '{}' not found in type '{}'", 
                    pos, field, ty)
            }
            MissingFields { fields, ty, pos } => {
                write!(f, "Type error at {}: missing fields {:?} in type '{}'", 
                    pos, fields, ty)
            }
            _ => write!(f, "Type error: {:?}", self),
        }
    }
}

impl std::error::Error for TypeError {}

/// 类型环境
#[derive(Debug, Clone)]
pub struct TypeEnv {
    /// 变量类型映射
    vars: HashMap<String, Type>,
    /// 函数类型映射
    funs: HashMap<String, Type>,
    /// 类型别名映射
    types: HashMap<String, Type>,
}

impl TypeEnv {
    /// 创建空类型环境
    pub fn new() -> Self {
        TypeEnv {
            vars: HashMap::new(),
            funs: HashMap::new(),
            types: HashMap::new(),
        }
    }

    /// 添加变量类型
    pub fn add_var(&mut self, name: &str, ty: Type) {
        self.vars.insert(name.to_string(), ty);
    }

    /// 添加函数类型
    pub fn add_fun(&mut self, name: &str, ty: Type) {
        self.funs.insert(name.to_string(), ty);
    }

    /// 添加类型别名
    pub fn add_type(&mut self, name: &str, ty: Type) {
        self.types.insert(name.to_string(), ty);
    }

    /// 查找变量类型
    pub fn get_var(&self, name: &str) -> Option<&Type> {
        self.vars.get(name)
    }

    /// 查找函数类型
    pub fn get_fun(&self, name: &str) -> Option<&Type> {
        self.funs.get(name)
    }

    /// 查找类型
    pub fn get_type(&self, name: &str) -> Option<&Type> {
        self.types.get(name)
    }

    /// 创建子环境（用于作用域）
    pub fn child(&self) -> Self {
        self.clone()
    }
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

/// 类型检查结果
#[derive(Debug, Clone)]
pub struct TypeCheckResult {
    pub ty: Type,
    pub errors: Vec<TypeError>,
}

/// 类型检查器
pub struct TypeChecker {
    env: TypeEnv,
    errors: Vec<TypeError>,
}

impl TypeChecker {
    /// 创建新的类型检查器
    pub fn new() -> Self {
        TypeChecker {
            env: TypeEnv::new(),
            errors: Vec::new(),
        }
    }

    /// 从环境创建类型检查器
    pub fn with_env(env: TypeEnv) -> Self {
        TypeChecker {
            env,
            errors: Vec::new(),
        }
    }

    /// 获取当前环境
    pub fn env(&self) -> &TypeEnv {
        &self.env
    }

    /// 添加内置类型
    pub fn add_builtins(&mut self) {
        // 内置函数
        self.env.add_fun("print", Type::fun(vec![Type::String], Type::Unit));
        self.env.add_fun("toString", Type::fun(vec![Type::Int], Type::String));
        self.env.add_fun("length", Type::fun(vec![Type::array(Type::Var("T".to_string()))], Type::Int));
    }

    /// 检查程序
    pub fn check_program(&mut self, program: &Program) -> Result<(), Vec<TypeError>> {
        self.errors.clear();

        // 第一遍：收集所有声明的类型签名
        for decl in program {
            if let Err(e) = self.collect_decl_signature(decl) {
                self.errors.push(e);
            }
        }

        // 第二遍：检查每个声明
        for decl in program {
            if let Err(e) = self.check_decl(decl) {
                self.errors.push(e);
            }
        }

        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(self.errors.clone())
        }
    }

    /// 收集声明的签名（用于处理前向引用）
    fn collect_decl_signature(&mut self, decl: &Decl) -> Result<(), TypeError> {
        match decl {
            Decl::Fun { name, params, ret_type, .. } => {
                let param_types: Vec<Type> = params.iter().map(|(_, ty)| ty.clone()).collect();
                let fun_type = Type::fun(param_types, ret_type.clone());
                self.env.add_fun(name, fun_type);
                Ok(())
            }
            Decl::TypeAlias { name, ty } => {
                self.env.add_type(name, ty.clone());
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// 检查单个声明
    fn check_decl(&mut self, decl: &Decl) -> Result<(), TypeError> {
        match decl {
            Decl::Let { name, ty, value } => {
                let value_type = self.check_expr(value)?;
                
                // 如果有类型注解，检查是否匹配
                if let Some(annotated) = ty {
                    if !self.types_match(annotated, &value_type) {
                        return Err(TypeError::TypeMismatch {
                            expected: annotated.clone(),
                            found: value_type,
                            pos: Position::default(),
                        });
                    }
                }
                
                self.env.add_var(name, value_type);
                Ok(())
            }
            Decl::Fun { name, params, ret_type, body, .. } => {
                // 创建新环境，包含参数
                let mut body_env = self.env.child();
                for (param_name, param_ty) in params {
                    body_env.add_var(param_name, param_ty.clone());
                }

                // 在函数体环境中检查
                let mut body_checker = TypeChecker::with_env(body_env);
                let body_type = body_checker.check_expr(body)?;

                // 检查返回类型
                if !self.types_match(ret_type, &body_type) {
                    return Err(TypeError::TypeMismatch {
                        expected: ret_type.clone(),
                        found: body_type,
                        pos: Position::default(),
                    });
                }

                Ok(())
            }
            Decl::TypeAlias { .. } => Ok(()), // 已在第一遍处理
        }
    }

    /// 检查表达式
    pub fn check_expr(&mut self, expr: &Expr) -> Result<Type, TypeError> {
        match expr {
            Expr::Int(_) => Ok(Type::Int),
            Expr::Bool(_) => Ok(Type::Bool),
            Expr::String(_) => Ok(Type::String),
            Expr::Unit => Ok(Type::Unit),
            
            Expr::Var(name) => {
                self.env.get_var(name)
                    .cloned()
                    .ok_or_else(|| TypeError::UndefinedVar {
                        name: name.clone(),
                        pos: Position::default(),
                    })
            }
            
            Expr::BinOp { op, left, right } => {
                self.check_binop(*op, left, right)
            }
            
            Expr::UnOp { op, operand } => {
                self.check_unop(*op, operand)
            }
            
            Expr::If { cond, then_branch, else_branch } => {
                self.check_if(cond, then_branch, else_branch)
            }
            
            Expr::Block(exprs) => {
                let mut last_type = Type::Unit;
                for expr in exprs {
                    last_type = self.check_expr(expr)?;
                }
                Ok(last_type)
            }
            
            Expr::Call { func, args } => {
                self.check_call(func, args)
            }
            
            Expr::Record(fields) => {
                let mut field_types = HashMap::new();
                for (name, expr) in fields {
                    field_types.insert(name.clone(), self.check_expr(expr)?);
                }
                Ok(Type::Record(field_types))
            }
            
            Expr::FieldAccess { expr, field } => {
                let expr_type = self.check_expr(expr)?;
                match expr_type {
                    Type::Record(ref fields) => {
                        fields.get(field)
                            .cloned()
                            .ok_or_else(|| TypeError::FieldNotFound {
                                field: field.clone(),
                                ty: expr_type,
                                pos: Position::default(),
                            })
                    }
                    _ => Err(TypeError::InvalidSyntax {
                        message: format!("Cannot access field '{}' on non-record type", field),
                        pos: Position::default(),
                    }),
                }
            }
            
            Expr::Array(elements) => {
                if elements.is_empty() {
                    Ok(Type::array(Type::Var("T".to_string())))
                } else {
                    let first_type = self.check_expr(&elements[0])?;
                    for elem in &elements[1..] {
                        let elem_type = self.check_expr(elem)?;
                        if !self.types_match(&first_type, &elem_type) {
                            return Err(TypeError::TypeMismatch {
                                expected: first_type,
                                found: elem_type,
                                pos: Position::default(),
                            });
                        }
                    }
                    Ok(Type::array(first_type))
                }
            }
            
            Expr::Index { expr, index } => {
                let expr_type = self.check_expr(expr)?;
                let index_type = self.check_expr(index)?;
                
                if !matches!(index_type, Type::Int) {
                    return Err(TypeError::TypeMismatch {
                        expected: Type::Int,
                        found: index_type,
                        pos: Position::default(),
                    });
                }
                
                match expr_type {
                    Type::Array(elem_type) => Ok(*elem_type),
                    _ => Err(TypeError::InvalidSyntax {
                        message: "Cannot index non-array type".to_string(),
                        pos: Position::default(),
                    }),
                }
            }
            
            Expr::Annotated { expr, ty } => {
                let expr_type = self.check_expr(expr)?;
                if self.types_match(ty, &expr_type) {
                    Ok(expr_type)
                } else {
                    Err(TypeError::TypeMismatch {
                        expected: ty.clone(),
                        found: expr_type,
                        pos: Position::default(),
                    })
                }
            }
        }
    }

    /// 检查二元运算
    fn check_binop(&mut self, op: BinOperator, left: &Expr, right: &Expr) -> Result<Type, TypeError> {
        let left_type = self.check_expr(left)?;
        let right_type = self.check_expr(right)?;

        use BinOperator::*;
        
        match op {
            // 算术运算：要求两个操作数都是 Int，结果也是 Int
            Add | Sub | Mul | Div | Mod => {
                if !matches!(left_type, Type::Int) {
                    return Err(TypeError::InvalidBinOp {
                        op,
                        left: left_type,
                        right: right_type,
                        pos: Position::default(),
                    });
                }
                if !matches!(right_type, Type::Int) {
                    return Err(TypeError::InvalidBinOp {
                        op,
                        left: left_type,
                        right: right_type,
                        pos: Position::default(),
                    });
                }
                Ok(Type::Int)
            }
            
            // 比较运算：要求两个操作数类型相同，结果是 Bool
            Eq | Ne => {
                if self.types_match(&left_type, &right_type) {
                    Ok(Type::Bool)
                } else {
                    Err(TypeError::InvalidBinOp {
                        op,
                        left: left_type,
                        right: right_type,
                        pos: Position::default(),
                    })
                }
            }
            
            // 关系运算：要求 Int，结果是 Bool
            Lt | Le | Gt | Ge => {
                if !matches!(left_type, Type::Int) || !matches!(right_type, Type::Int) {
                    return Err(TypeError::InvalidBinOp {
                        op,
                        left: left_type,
                        right: right_type,
                        pos: Position::default(),
                    });
                }
                Ok(Type::Bool)
            }
            
            // 逻辑运算：要求 Bool，结果是 Bool
            And | Or => {
                if !matches!(left_type, Type::Bool) || !matches!(right_type, Type::Bool) {
                    return Err(TypeError::InvalidBinOp {
                        op,
                        left: left_type,
                        right: right_type,
                        pos: Position::default(),
                    });
                }
                Ok(Type::Bool)
            }
        }
    }

    /// 检查一元运算
    fn check_unop(&mut self, op: UnOperator, operand: &Expr) -> Result<Type, TypeError> {
        let operand_type = self.check_expr(operand)?;

        match op {
            UnOperator::Neg => {
                if !matches!(operand_type, Type::Int) {
                    return Err(TypeError::InvalidUnOp {
                        op,
                        operand: operand_type,
                        pos: Position::default(),
                    });
                }
                Ok(Type::Int)
            }
            UnOperator::Not => {
                if !matches!(operand_type, Type::Bool) {
                    return Err(TypeError::InvalidUnOp {
                        op,
                        operand: operand_type,
                        pos: Position::default(),
                    });
                }
                Ok(Type::Bool)
            }
        }
    }

    /// 检查条件表达式
    fn check_if(&mut self, cond: &Expr, then_branch: &Expr, else_branch: &Expr) -> Result<Type, TypeError> {
        let cond_type = self.check_expr(cond)?;
        
        if !matches!(cond_type, Type::Bool) {
            return Err(TypeError::TypeMismatch {
                expected: Type::Bool,
                found: cond_type,
                pos: Position::default(),
            });
        }

        let then_type = self.check_expr(then_branch)?;
        let else_type = self.check_expr(else_branch)?;

        if self.types_match(&then_type, &else_type) {
            Ok(then_type)
        } else {
            Err(TypeError::BranchTypeMismatch {
                then_type,
                else_type,
                pos: Position::default(),
            })
        }
    }

    /// 检查函数调用
    fn check_call(&mut self, func: &Expr, args: &[Expr]) -> Result<Type, TypeError> {
        let func_type = self.check_expr(func)?;

        match func_type {
            Type::Fun { params, ret } => {
                if params.len() != args.len() {
                    return Err(TypeError::ArgCountMismatch {
                        expected: params.len(),
                        found: args.len(),
                        pos: Position::default(),
                    });
                }

                for (param_ty, arg) in params.iter().zip(args.iter()) {
                    let arg_ty = self.check_expr(arg)?;
                    if !self.types_match(param_ty, &arg_ty) {
                        return Err(TypeError::TypeMismatch {
                            expected: param_ty.clone(),
                            found: arg_ty,
                            pos: Position::default(),
                        });
                    }
                }

                Ok(*ret)
            }
            _ => Err(TypeError::NotCallable {
                ty: func_type,
                pos: Position::default(),
            }),
        }
    }

    /// 检查类型是否匹配
    fn types_match(&self, expected: &Type, found: &Type) -> bool {
        match (expected, found) {
            // 基础类型直接比较
            (Type::Int, Type::Int) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::String, Type::String) => true,
            (Type::Unit, Type::Unit) => true,
            
            // 函数类型：参数和返回类型都匹配
            (Type::Fun { params: p1, ret: r1 }, Type::Fun { params: p2, ret: r2 }) => {
                p1.len() == p2.len()
                    && p1.iter().zip(p2.iter()).all(|(a, b)| self.types_match(a, b))
                    && self.types_match(r1, r2)
            }
            
            // 数组类型：元素类型匹配
            (Type::Array(e1), Type::Array(e2)) => self.types_match(e1, e2),
            
            // 元组类型
            (Type::Tuple(t1), Type::Tuple(t2)) => {
                t1.len() == t2.len()
                    && t1.iter().zip(t2.iter()).all(|(a, b)| self.types_match(a, b))
            }
            
            // 记录类型：字段数量和类型都匹配
            (Type::Record(r1), Type::Record(r2)) => {
                r1.len() == r2.len()
                    && r1.iter().all(|(name, ty1)| {
                        r2.get(name).map_or(false, |ty2| self.types_match(ty1, ty2))
                    })
            }
            
            // 类型变量可以匹配任何类型（用于泛型）
            (Type::Var(_), _) => true,
            (_, Type::Var(_)) => true,
            
            _ => false,
        }
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

/// 便捷的类型检查函数
pub fn check(program: &Program) -> Result<(), Vec<TypeError>> {
    let mut checker = TypeChecker::new();
    checker.add_builtins();
    checker.check_program(program)
}

/// 显示所有类型错误
pub fn print_errors(errors: &[TypeError]) {
    for error in errors {
        eprintln!("{}", error);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::utils::*;

    #[test]
    fn test_check_int() {
        let mut checker = TypeChecker::new();
        let ty = checker.check_expr(&int(42)).unwrap();
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn test_check_arithmetic() {
        let mut checker = TypeChecker::new();
        let expr = binop(BinOperator::Add, int(1), int(2));
        let ty = checker.check_expr(&expr).unwrap();
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn test_type_mismatch() {
        let mut checker = TypeChecker::new();
        // 不能将 Int 和 Bool 相加
        let expr = binop(BinOperator::Add, int(1), bool(true));
        assert!(checker.check_expr(&expr).is_err());
    }

    #[test]
    fn test_check_function() {
        let program = vec![
            Decl::Fun {
                name: "add".to_string(),
                generics: vec![],
                params: vec![
                    ("x".to_string(), Type::Int),
                    ("y".to_string(), Type::Int),
                ],
                ret_type: Type::Int,
                body: Expr::BinOp {
                    op: BinOperator::Add,
                    left: Box::new(var("x")),
                    right: Box::new(var("y")),
                },
            },
        ];

        let result = check(&program);
        assert!(result.is_ok());
    }

    #[test]
    fn test_undefined_variable() {
        let mut checker = TypeChecker::new();
        let expr = var("undefined_var");
        assert!(checker.check_expr(&expr).is_err());
    }

    #[test]
    fn test_if_type_mismatch() {
        let mut checker = TypeChecker::new();
        let expr = Expr::If {
            cond: Box::new(bool(true)),
            then_branch: Box::new(int(1)),
            else_branch: Box::new(bool(false)),
        };
        assert!(checker.check_expr(&expr).is_err());
    }
}
