//! # Hindley-Milner 类型推导实现
//! 
//! 实现 Hindley-Milner 类型推导算法，支持：
//! - 多态类型
//! - let 多态
//! - 统一算法

use std::collections::{HashMap, HashSet};

/// 类型变量 ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVar(pub u64);

impl TypeVar {
    pub fn fresh(counter: &mut u64) -> Self {
        *counter += 1;
        TypeVar(*counter)
    }
}

impl std::fmt::Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "t{}", self.0)
    }
}

/// 多态类型
#[derive(Debug, Clone, PartialEq)]
pub enum PolyType {
    /// 单态类型
    Mono(MonoType),
    /// 全称量词: ∀α. T
    Forall(Vec<TypeVar>, Box<PolyType>),
}

/// 单态类型
#[derive(Debug, Clone, PartialEq)]
pub enum MonoType {
    /// 类型变量
    Var(TypeVar),
    /// 具体类型（如 Int, Bool）
    Concrete(String),
    /// 函数类型: T1 -> T2
    Arrow(Box<MonoType>, Box<MonoType>),
}

impl MonoType {
    /// 创建函数类型
    pub fn arrow(from: MonoType, to: MonoType) -> Self {
        MonoType::Arrow(Box::new(from), Box::new(to))
    }

    /// 获取类型中的自由变量
    pub fn free_vars(&self) -> HashSet<TypeVar> {
        let mut vars = HashSet::new();
        self.collect_free_vars(&mut vars);
        vars
    }

    fn collect_free_vars(&self, vars: &mut HashSet<TypeVar>) {
        match self {
            MonoType::Var(v) => { vars.insert(*v); }
            MonoType::Concrete(_) => {}
            MonoType::Arrow(from, to) => {
                from.collect_free_vars(vars);
                to.collect_free_vars(vars);
            }
        }
    }

    /// 应用替换
    pub fn apply_subst(&self, subst: &Substitution) -> Self {
        match self {
            MonoType::Var(v) => subst.get(v).cloned().unwrap_or(MonoType::Var(*v)),
            MonoType::Concrete(_) => self.clone(),
            MonoType::Arrow(from, to) => {
                MonoType::arrow(from.apply_subst(subst), to.apply_subst(subst))
            }
        }
    }
}

impl PolyType {
    /// 获取类型中的自由变量
    pub fn free_vars(&self) -> HashSet<TypeVar> {
        let mut vars = HashSet::new();
        self.collect_free_vars(&mut vars);
        vars
    }

    fn collect_free_vars(&self, vars: &mut HashSet<TypeVar>) {
        match self {
            PolyType::Mono(m) => {
                vars.extend(m.free_vars());
            }
            PolyType::Forall(bound, body) => {
                let mut body_vars = HashSet::new();
                body.collect_free_vars(&mut body_vars);
                for v in bound {
                    body_vars.remove(v);
                }
                vars.extend(body_vars);
            }
        }
    }

    /// 实例化：将多态类型转换为单态类型，用新变量替换量词变量
    pub fn instantiate(&self, counter: &mut u64) -> MonoType {
        match self {
            PolyType::Mono(m) => m.clone(),
            PolyType::Forall(vars, body) => {
                let mut subst = Substitution::new();
                for v in vars {
                    subst.insert(*v, MonoType::Var(TypeVar::fresh(counter)));
                }
                body.instantiate(counter).apply_subst(&subst)
            }
        }
    }

    /// 应用替换
    pub fn apply_subst(&self, subst: &Substitution) -> Self {
        match self {
            PolyType::Mono(m) => PolyType::Mono(m.apply_subst(subst)),
            PolyType::Forall(bound, body) => {
                // 移除对绑定变量的替换
                let mut new_subst = subst.clone();
                for v in bound {
                    new_subst.remove(v);
                }
                PolyType::Forall(bound.clone(), Box::new(body.apply_subst(&new_subst)))
            }
        }
    }
}

/// 替换：将类型变量映射到单态类型
#[derive(Debug, Clone, Default)]
pub struct Substitution {
    mapping: HashMap<TypeVar, MonoType>,
}

impl Substitution {
    pub fn new() -> Self {
        Self {
            mapping: HashMap::new(),
        }
    }

    pub fn insert(&mut self, var: TypeVar, ty: MonoType) {
        // 应用已有替换到新类型
        let ty = ty.apply_subst(self);
        self.mapping.insert(var, ty);
    }

    pub fn get(&self, var: &TypeVar) -> Option<&MonoType> {
        self.mapping.get(var)
    }

    pub fn remove(&mut self, var: &TypeVar) {
        self.mapping.remove(var);
    }

    /// 组合两个替换
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result = self.clone();
        for (var, ty) in &other.mapping {
            result.insert(*var, ty.apply_subst(self));
        }
        result
    }
}

/// 类型环境
#[derive(Debug, Clone, Default)]
pub struct TypeEnvironment {
    bindings: HashMap<String, PolyType>,
}

impl TypeEnvironment {
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
        }
    }

    pub fn extend(&mut self, name: impl Into<String>, ty: PolyType) {
        self.bindings.insert(name.into(), ty);
    }

    pub fn get(&self, name: &str) -> Option<&PolyType> {
        self.bindings.get(name)
    }

    pub fn apply_subst(&mut self, subst: &Substitution) {
        for (_, ty) in &mut self.bindings {
            *ty = ty.apply_subst(subst);
        }
    }

    /// 获取环境中的自由类型变量
    pub fn free_vars(&self) -> HashSet<TypeVar> {
        let mut vars = HashSet::new();
        for (_, ty) in &self.bindings {
            vars.extend(ty.free_vars());
        }
        vars
    }
}

/// 表达式
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var(String),
    Int(i64),
    Bool(bool),
    Lambda {
        param: String,
        body: Box<Expr>,
    },
    App {
        func: Box<Expr>,
        arg: Box<Expr>,
    },
    Let {
        name: String,
        value: Box<Expr>,
        body: Box<Expr>,
    },
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },
}

/// 类型检查器
pub struct TypeChecker {
    var_counter: u64,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self { var_counter: 0 }
    }

    /// 类型推断主函数
    pub fn infer(&mut self, expr: &Expr, env: &mut TypeEnvironment) -> Result<MonoType, TypeError> {
        let (ty, subst) = self.infer_internal(expr, env)?;
        Ok(ty.apply_subst(&subst))
    }

    fn infer_internal(
        &mut self,
        expr: &Expr,
        env: &mut TypeEnvironment,
    ) -> Result<(MonoType, Substitution), TypeError> {
        match expr {
            Expr::Var(name) => {
                let ty = env
                    .get(name)
                    .ok_or_else(|| TypeError::UnboundVariable(name.clone()))?
                    .clone()
                    .instantiate(&mut self.var_counter);
                Ok((ty, Substitution::new()))
            }
            Expr::Int(_) => Ok((MonoType::Concrete("Int".to_string()), Substitution::new())),
            Expr::Bool(_) => Ok((MonoType::Concrete("Bool".to_string()), Substitution::new())),
            Expr::Lambda { param, body } => {
                let param_ty = MonoType::Var(TypeVar::fresh(&mut self.var_counter));
                let mut new_env = env.clone();
                new_env.extend(param.clone(), PolyType::Mono(param_ty.clone()));
                
                let (body_ty, subst) = self.infer_internal(body, &mut new_env)?;
                let param_ty = param_ty.apply_subst(&subst);
                let func_ty = MonoType::arrow(param_ty, body_ty);
                Ok((func_ty, subst))
            }
            Expr::App { func, arg } => {
                let (func_ty, s1) = self.infer_internal(func, env)?;
                let mut env2 = env.clone();
                env2.apply_subst(&s1);
                let (arg_ty, s2) = self.infer_internal(arg, &mut env2)?;
                
                let func_ty = func_ty.apply_subst(&s2);
                let result_ty = MonoType::Var(TypeVar::fresh(&mut self.var_counter));
                
                let s3 = unify(&func_ty, &MonoType::arrow(arg_ty, result_ty.clone()))?;
                let final_subst = s3.compose(&s2.compose(&s1));
                let final_ty = result_ty.apply_subst(&final_subst);
                
                Ok((final_ty, final_subst))
            }
            Expr::Let { name, value, body } => {
                let (value_ty, s1) = self.infer_internal(value, env)?;
                let mut env2 = env.clone();
                env2.apply_subst(&s1);
                
                // 泛化：将自由类型变量变为多态
                let gen_ty = self.generalize(&value_ty, &env2);
                env2.extend(name.clone(), gen_ty);
                
                let (body_ty, s2) = self.infer_internal(body, &mut env2)?;
                let final_subst = s2.compose(&s1);
                Ok((body_ty, final_subst))
            }
            Expr::If { cond, then_branch, else_branch } => {
                let (cond_ty, s1) = self.infer_internal(cond, env)?;
                let s_bool = unify(&cond_ty, &MonoType::Concrete("Bool".to_string()))?;
                
                let mut env2 = env.clone();
                env2.apply_subst(&s1.compose(&s_bool));
                
                let (then_ty, s2) = self.infer_internal(then_branch, &mut env2)?;
                let mut env3 = env.clone();
                env3.apply_subst(&s1.compose(&s_bool).compose(&s2));
                
                let (else_ty, s3) = self.infer_internal(else_branch, &mut env3)?;
                
                let then_ty = then_ty.apply_subst(&s3);
                let s4 = unify(&then_ty, &else_ty)?;
                
                let final_subst = s4.compose(&s3.compose(&s2.compose(&s1.compose(&s_bool))));
                Ok((then_ty.apply_subst(&s4), final_subst))
            }
        }
    }

    /// 泛化：将类型中的自由变量变为全称量词
    fn generalize(&mut self, ty: &MonoType, env: &TypeEnvironment) -> PolyType {
        let env_vars = env.free_vars();
        let ty_vars: Vec<_> = ty
            .free_vars()
            .difference(&env_vars)
            .cloned()
            .collect();
        
        if ty_vars.is_empty() {
            PolyType::Mono(ty.clone())
        } else {
            PolyType::Forall(ty_vars, Box::new(PolyType::Mono(ty.clone())))
        }
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

/// 统一两个类型
pub fn unify(t1: &MonoType, t2: &MonoType) -> Result<Substitution, TypeError> {
    match (t1, t2) {
        (MonoType::Var(v1), MonoType::Var(v2)) if v1 == v2 => Ok(Substitution::new()),
        (MonoType::Var(v), t) | (t, MonoType::Var(v)) => {
            if occurs_in(*v, t) {
                Err(TypeError::OccursCheck(*v, t.clone()))
            } else {
                let mut subst = Substitution::new();
                subst.insert(*v, t.clone());
                Ok(subst)
            }
        }
        (MonoType::Concrete(c1), MonoType::Concrete(c2)) if c1 == c2 => {
            Ok(Substitution::new())
        }
        (MonoType::Arrow(from1, to1), MonoType::Arrow(from2, to2)) => {
            let s1 = unify(from1, from2)?;
            let to1 = to1.apply_subst(&s1);
            let to2 = to2.apply_subst(&s1);
            let s2 = unify(&to1, &to2)?;
            Ok(s2.compose(&s1))
        }
        _ => Err(TypeError::UnificationFailed(t1.clone(), t2.clone())),
    }
}

/// 检查变量是否出现在类型中（Occurs Check）
fn occurs_in(var: TypeVar, ty: &MonoType) -> bool {
    ty.free_vars().contains(&var)
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    UnboundVariable(String),
    UnificationFailed(MonoType, MonoType),
    OccursCheck(TypeVar, MonoType),
}

/// 便捷构造器
pub mod builder {
    use super::*;

    pub fn var(name: impl Into<String>) -> Expr {
        Expr::Var(name.into())
    }

    pub fn int(n: i64) -> Expr {
        Expr::Int(n)
    }

    pub fn bool_(b: bool) -> Expr {
        Expr::Bool(b)
    }

    pub fn lambda(param: impl Into<String>, body: Expr) -> Expr {
        Expr::Lambda {
            param: param.into(),
            body: Box::new(body),
        }
    }

    pub fn app(func: Expr, arg: Expr) -> Expr {
        Expr::App {
            func: Box::new(func),
            arg: Box::new(arg),
        }
    }

    pub fn let_(name: impl Into<String>, value: Expr, body: Expr) -> Expr {
        Expr::Let {
            name: name.into(),
            value: Box::new(value),
            body: Box::new(body),
        }
    }

    pub fn if_(cond: Expr, then_branch: Expr, else_branch: Expr) -> Expr {
        Expr::If {
            cond: Box::new(cond),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::builder::*;

    #[test]
    fn test_infer_int() {
        let mut tc = TypeChecker::new();
        let ty = tc.infer(&int(42), &mut TypeEnvironment::new()).unwrap();
        assert_eq!(ty, MonoType::Concrete("Int".to_string()));
    }

    #[test]
    fn test_infer_lambda() {
        // λx. x
        let id = lambda("x", var("x"));
        let mut tc = TypeChecker::new();
        let ty = tc.infer(&id, &mut TypeEnvironment::new()).unwrap();
        
        // 结果应该是 t1 -> t1
        match ty {
            MonoType::Arrow(from, to) => {
                assert_eq!(from, to);
            }
            _ => panic!("Expected arrow type"),
        }
    }

    #[test]
    fn test_infer_let_polymorphism() {
        // let id = λx. x in (id 5, id true)
        let id = lambda("x", var("x"));
        let expr = let_(
            "id",
            id,
            app(app(var("id"), int(5)), var("id"))
        );
        
        let mut tc = TypeChecker::new();
        // 这个会失败，因为我们不能应用一个整数
        // 修正：let id = λx. x in id id 5
        let expr2 = let_(
            "id",
            lambda("x", var("x")),
            app(app(var("id"), var("id")), int(5))
        );
        
        let ty = tc.infer(&expr2, &mut TypeEnvironment::new()).unwrap();
        assert_eq!(ty, MonoType::Concrete("Int".to_string()));
    }

    #[test]
    fn test_unify() {
        let t1 = MonoType::arrow(MonoType::Var(TypeVar(1)), MonoType::Var(TypeVar(2)));
        let t2 = MonoType::arrow(MonoType::Concrete("Int".to_string()), MonoType::Var(TypeVar(3)));
        
        let subst = unify(&t1, &t2).unwrap();
        assert_eq!(subst.get(&TypeVar(1)), Some(&MonoType::Concrete("Int".to_string())));
    }

    #[test]
    fn test_occurs_check() {
        let t = MonoType::arrow(MonoType::Var(TypeVar(1)), MonoType::Var(TypeVar(2)));
        let result = unify(&MonoType::Var(TypeVar(1)), &t);
        assert!(matches!(result, Err(TypeError::OccursCheck(..))));
    }
}
