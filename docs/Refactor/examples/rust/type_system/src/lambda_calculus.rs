//! # Lambda 演算实现
//! 
//! 实现简单类型 lambda 演算，包括：
//! - 项 (Terms)
//! - 类型 (Types)
//! - 求值 (Evaluation)
//! - 替换 (Substitution)

use std::collections::HashMap;

/// Lambda 项
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// 变量
    Var(String),
    /// 抽象: λx:T. body
    Abs {
        var: String,
        ty: Type,
        body: Box<Term>,
    },
    /// 应用: (func arg)
    App {
        func: Box<Term>,
        arg: Box<Term>,
    },
    /// 常量
    Const(i64),
}

/// 简单类型
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    /// 整数类型
    Int,
    /// 函数类型: T1 -> T2
    Arrow(Box<Type>, Box<Type>),
    /// 类型变量
    Var(String),
}

impl Type {
    /// 创建函数类型
    pub fn arrow(from: Type, to: Type) -> Self {
        Type::Arrow(Box::new(from), Box::new(to))
    }
}

/// 类型环境
pub type TypeEnv = HashMap<String, Type>;

/// Lambda 演算解释器
pub struct LambdaCalculus;

impl LambdaCalculus {
    /// 创建一个新的解释器
    pub fn new() -> Self {
        Self
    }

    /// 类型检查
    pub fn type_check(&self, term: &Term, env: &TypeEnv) -> Result<Type, TypeError> {
        match term {
            Term::Var(x) => {
                env.get(x)
                    .cloned()
                    .ok_or_else(|| TypeError::UnboundVariable(x.clone()))
            }
            Term::Abs { var, ty, body } => {
                let mut new_env = env.clone();
                new_env.insert(var.clone(), ty.clone());
                let body_ty = self.type_check(body, &new_env)?;
                Ok(Type::arrow(ty.clone(), body_ty))
            }
            Term::App { func, arg } => {
                let func_ty = self.type_check(func, env)?;
                let arg_ty = self.type_check(arg, env)?;

                match func_ty {
                    Type::Arrow(from, to) => {
                        if *from == arg_ty {
                            Ok(*to)
                        } else {
                            Err(TypeError::TypeMismatch {
                                expected: *from,
                                got: arg_ty,
                            })
                        }
                    }
                    _ => Err(TypeError::NotAFunction(func_ty)),
                }
            }
            Term::Const(_) => Ok(Type::Int),
        }
    }

    /// 求值（大步骤语义）
    pub fn eval(&self, term: &Term) -> Result<Term, EvalError> {
        match term {
            Term::Var(x) => Err(EvalError::UnboundVariable(x.clone())),
            Term::Abs { .. } => Ok(term.clone()),
            Term::App { func, arg } => {
                let func_val = self.eval(func)?;
                let arg_val = self.eval(arg)?;

                match func_val {
                    Term::Abs { var, body, .. } => {
                        let substituted = self.substitute(&body, &var, &arg_val);
                        self.eval(&substituted)
                    }
                    _ => Err(EvalError::NotAFunction),
                }
            }
            Term::Const(_) => Ok(term.clone()),
        }
    }

    /// 替换: [t/x]body
    pub fn substitute(&self, body: &Term, var: &str, replacement: &Term) -> Term {
        match body {
            Term::Var(x) if x == var => replacement.clone(),
            Term::Var(_) => body.clone(),
            Term::Abs { var: x, ty, body: b } if x != var => {
                // 避免变量捕获
                if self.free_vars(replacement).contains(x) {
                    let new_var = self.fresh_var(x);
                    let new_body = self.substitute(b, x, &Term::Var(new_var.clone()));
                    Term::Abs {
                        var: new_var,
                        ty: ty.clone(),
                        body: Box::new(self.substitute(&new_body, var, replacement)),
                    }
                } else {
                    Term::Abs {
                        var: x.clone(),
                        ty: ty.clone(),
                        body: Box::new(self.substitute(b, var, replacement)),
                    }
                }
            }
            Term::Abs { .. } => body.clone(),
            Term::App { func, arg } => Term::App {
                func: Box::new(self.substitute(func, var, replacement)),
                arg: Box::new(self.substitute(arg, var, replacement)),
            },
            Term::Const(_) => body.clone(),
        }
    }

    /// 获取自由变量
    fn free_vars(&self, term: &Term) -> std::collections::HashSet<String> {
        let mut vars = std::collections::HashSet::new();
        self.collect_free_vars(term, &mut vars);
        vars
    }

    fn collect_free_vars(&self, term: &Term, vars: &mut std::collections::HashSet<String>) {
        match term {
            Term::Var(x) => { vars.insert(x.clone()); }
            Term::Abs { var, body, .. } => {
                let mut body_vars = std::collections::HashSet::new();
                self.collect_free_vars(body, &mut body_vars);
                body_vars.remove(var);
                vars.extend(body_vars);
            }
            Term::App { func, arg } => {
                self.collect_free_vars(func, vars);
                self.collect_free_vars(arg, vars);
            }
            Term::Const(_) => {}
        }
    }

    /// 生成新变量名
    fn fresh_var(&self, base: &str) -> String {
        format!("{}_{}", base, rand::random::<u32>())
    }
}

impl Default for LambdaCalculus {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    UnboundVariable(String),
    TypeMismatch { expected: Type, got: Type },
    NotAFunction(Type),
}

#[derive(Debug, Clone, PartialEq)]
pub enum EvalError {
    UnboundVariable(String),
    NotAFunction,
}

/// 便捷的项构造函数
pub mod builder {
    use super::*;

    pub fn var(name: impl Into<String>) -> Term {
        Term::Var(name.into())
    }

    pub fn abs(var: impl Into<String>, ty: Type, body: Term) -> Term {
        Term::Abs {
            var: var.into(),
            ty,
            body: Box::new(body),
        }
    }

    pub fn app(func: Term, arg: Term) -> Term {
        Term::App {
            func: Box::new(func),
            arg: Box::new(arg),
        }
    }

    pub fn int(n: i64) -> Term {
        Term::Const(n)
    }

    pub fn int_ty() -> Type {
        Type::Int
    }

    pub fn arrow(from: Type, to: Type) -> Type {
        Type::arrow(from, to)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::builder::*;

    #[test]
    fn test_type_check_identity() {
        // λx:Int. x
        let id = abs("x", int_ty(), var("x"));
        let lc = LambdaCalculus::new();
        let ty = lc.type_check(&id, &TypeEnv::new()).unwrap();
        
        assert_eq!(ty, arrow(int_ty(), int_ty()));
    }

    #[test]
    fn test_type_check_application() {
        // (λx:Int. x) 5
        let id = abs("x", int_ty(), var("x"));
        let app = app(id, int(5));
        let lc = LambdaCalculus::new();
        let ty = lc.type_check(&app, &TypeEnv::new()).unwrap();
        
        assert_eq!(ty, int_ty());
    }

    #[test]
    fn test_type_check_const() {
        let lc = LambdaCalculus::new();
        let ty = lc.type_check(&int(42), &TypeEnv::new()).unwrap();
        assert_eq!(ty, int_ty());
    }

    #[test]
    fn test_eval_identity() {
        // (λx:Int. x) 5 → 5
        let id = abs("x", int_ty(), var("x"));
        let app = app(id, int(5));
        let lc = LambdaCalculus::new();
        let result = lc.eval(&app).unwrap();
        
        assert_eq!(result, int(5));
    }

    #[test]
    fn test_substitution() {
        // [5/x](x) = 5
        let lc = LambdaCalculus::new();
        let result = lc.substitute(&var("x"), "x", &int(5));
        assert_eq!(result, int(5));

        // [5/x](λy:Int. x) = λy:Int. 5
        let body = abs("y", int_ty(), var("x"));
        let result = lc.substitute(&body, "x", &int(5));
        assert_eq!(result, abs("y", int_ty(), int(5)));
    }

    #[test]
    fn test_type_error() {
        // (λx:Int. x) (λy:Int. y) - 类型错误
        let id = abs("x", int_ty(), var("x"));
        let id2 = abs("y", int_ty(), var("y"));
        let app = app(id, id2);
        let lc = LambdaCalculus::new();
        let result = lc.type_check(&app, &TypeEnv::new());
        
        assert!(matches!(result, Err(TypeError::TypeMismatch { .. })));
    }
}
