//! 递归下降解析器
//! 
//! 将源代码解析为 AST。支持表达式、声明和类型注解。

use crate::ast::*;
use std::collections::HashMap;

/// 解析错误类型
#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    UnexpectedToken { expected: String, found: String, pos: Position },
    UnexpectedEOF { expected: String },
    InvalidNumber { text: String, pos: Position },
    InvalidSyntax { message: String, pos: Position },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::UnexpectedToken { expected, found, pos } => {
                write!(f, "Parse error at {}: expected '{}', found '{}'", pos, expected, found)
            }
            ParseError::UnexpectedEOF { expected } => {
                write!(f, "Parse error: unexpected end of file, expected '{}'", expected)
            }
            ParseError::InvalidNumber { text, pos } => {
                write!(f, "Parse error at {}: invalid number '{}'", pos, text)
            }
            ParseError::InvalidSyntax { message, pos } => {
                write!(f, "Parse error at {}: {}", pos, message)
            }
        }
    }
}

use std::fmt;

/// 词法单元类型
#[derive(Debug, Clone, PartialEq)]
enum Token {
    // 关键字
    Let,
    Fn,
    Type,
    If,
    Then,
    Else,
    True,
    False,
    
    // 类型
    TInt,
    TBool,
    TString,
    TUnit,
    
    // 标识符和常量
    Ident(String),
    Int(i64),
    String(String),
    
    // 运算符
    Plus, Minus, Star, Slash, Percent,
    Eq, Ne, Lt, Le, Gt, Ge,
    And, Or, Not,
    Assign,
    Arrow,    // ->
    
    // 分隔符
    LParen, RParen,
    LBrace, RBrace,
    LBracket, RBracket,
    Comma, Semicolon, Colon,
    
    // 特殊
    NewLine,
    EOF,
}

/// 词法分析器
struct Lexer {
    input: Vec<char>,
    pos: usize,
    line: usize,
    column: usize,
}

impl Lexer {
    fn new(input: &str) -> Self {
        Lexer {
            input: input.chars().collect(),
            pos: 0,
            line: 1,
            column: 1,
        }
    }

    fn current(&self) -> Option<char> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) -> Option<char> {
        let ch = self.current()?;
        self.pos += 1;
        if ch == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(ch)
    }

    fn peek(&self, offset: usize) -> Option<char> {
        self.input.get(self.pos + offset).copied()
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.current() {
            if ch.is_whitespace() && ch != '\n' {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn skip_comment(&mut self) {
        if self.current() == Some('/') && self.peek(1) == Some('/') {
            while let Some(ch) = self.current() {
                if ch == '\n' {
                    break;
                }
                self.advance();
            }
        }
    }

    fn read_identifier(&mut self) -> String {
        let mut result = String::new();
        while let Some(ch) = self.current() {
            if ch.is_alphanumeric() || ch == '_' {
                result.push(ch);
                self.advance();
            } else {
                break;
            }
        }
        result
    }

    fn read_number(&mut self) -> Result<Token, ParseError> {
        let start_pos = Position { line: self.line, column: self.column };
        let mut result = String::new();
        
        while let Some(ch) = self.current() {
            if ch.is_ascii_digit() {
                result.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        match result.parse::<i64>() {
            Ok(n) => Ok(Token::Int(n)),
            Err(_) => Err(ParseError::InvalidNumber {
                text: result,
                pos: start_pos,
            }),
        }
    }

    fn read_string(&mut self) -> Result<Token, ParseError> {
        self.advance(); // 跳过开头的 "
        let mut result = String::new();
        
        while let Some(ch) = self.current() {
            if ch == '"' {
                self.advance();
                return Ok(Token::String(result));
            } else if ch == '\\' {
                self.advance();
                match self.current() {
                    Some('n') => result.push('\n'),
                    Some('t') => result.push('\t'),
                    Some('\\') => result.push('\\'),
                    Some('"') => result.push('"'),
                    _ => {}
                }
                self.advance();
            } else {
                result.push(ch);
                self.advance();
            }
        }
        
        Err(ParseError::UnexpectedEOF { expected: "\"".to_string() })
    }

    fn next_token(&mut self) -> Result<Token, ParseError> {
        self.skip_whitespace();
        self.skip_comment();
        self.skip_whitespace();

        let pos = Position { line: self.line, column: self.column };

        match self.current() {
            None => Ok(Token::EOF),
            Some('\n') => {
                self.advance();
                Ok(Token::NewLine)
            }
            
            // 标识符和关键字
            Some(ch) if ch.is_alphabetic() || ch == '_' => {
                let ident = self.read_identifier();
                let token = match ident.as_str() {
                    "let" => Token::Let,
                    "fn" => Token::Fn,
                    "type" => Token::Type,
                    "if" => Token::If,
                    "then" => Token::Then,
                    "else" => Token::Else,
                    "true" => Token::True,
                    "false" => Token::False,
                    "Int" => Token::TInt,
                    "Bool" => Token::TBool,
                    "String" => Token::TString,
                    "Unit" => Token::TUnit,
                    _ => Token::Ident(ident),
                };
                Ok(token)
            }
            
            // 数字
            Some(ch) if ch.is_ascii_digit() => self.read_number(),
            
            // 字符串
            Some('"') => self.read_string(),
            
            // 运算符和分隔符
            Some('+') => { self.advance(); Ok(Token::Plus) }
            Some('-') => {
                self.advance();
                if self.current() == Some('>') {
                    self.advance();
                    Ok(Token::Arrow)
                } else {
                    Ok(Token::Minus)
                }
            }
            Some('*') => { self.advance(); Ok(Token::Star) }
            Some('/') => { self.advance(); Ok(Token::Slash) }
            Some('%') => { self.advance(); Ok(Token::Percent) }
            
            Some('=') => {
                self.advance();
                if self.current() == Some('=') {
                    self.advance();
                    Ok(Token::Eq)
                } else {
                    Ok(Token::Assign)
                }
            }
            Some('!') => {
                self.advance();
                if self.current() == Some('=') {
                    self.advance();
                    Ok(Token::Ne)
                } else {
                    Ok(Token::Not)
                }
            }
            Some('<') => {
                self.advance();
                if self.current() == Some('=') {
                    self.advance();
                    Ok(Token::Le)
                } else {
                    Ok(Token::Lt)
                }
            }
            Some('>') => {
                self.advance();
                if self.current() == Some('=') {
                    self.advance();
                    Ok(Token::Ge)
                } else {
                    Ok(Token::Gt)
                }
            }
            Some('&') => {
                self.advance();
                if self.current() == Some('&') {
                    self.advance();
                    Ok(Token::And)
                } else {
                    Err(ParseError::InvalidSyntax {
                        message: format!("Unexpected character '&'"),
                        pos,
                    })
                }
            }
            Some('|') => {
                self.advance();
                if self.current() == Some('|') {
                    self.advance();
                    Ok(Token::Or)
                } else {
                    Err(ParseError::InvalidSyntax {
                        message: format!("Unexpected character '|'"),
                        pos,
                    })
                }
            }
            
            Some('(') => { self.advance(); Ok(Token::LParen) }
            Some(')') => { self.advance(); Ok(Token::RParen) }
            Some('{') => { self.advance(); Ok(Token::LBrace) }
            Some('}') => { self.advance(); Ok(Token::RBrace) }
            Some('[') => { self.advance(); Ok(Token::LBracket) }
            Some(']') => { self.advance(); Ok(Token::RBracket) }
            Some(',') => { self.advance(); Ok(Token::Comma) }
            Some(';') => { self.advance(); Ok(Token::Semicolon) }
            Some(':') => { self.advance(); Ok(Token::Colon) }
            
            Some(ch) => Err(ParseError::InvalidSyntax {
                message: format!("Unexpected character '{}'", ch),
                pos,
            }),
        }
    }
}

/// 解析器
pub struct Parser {
    lexer: Lexer,
    current: Token,
}

impl Parser {
    /// 创建新解析器
    pub fn new(input: &str) -> Result<Self, ParseError> {
        let mut lexer = Lexer::new(input);
        let current = lexer.next_token()?;
        Ok(Parser { lexer, current })
    }

    /// 解析完整程序
    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut decls = Vec::new();
        
        while self.current != Token::EOF {
            self.skip_newlines();
            if self.current == Token::EOF {
                break;
            }
            decls.push(self.parse_decl()?);
            self.skip_newlines();
        }
        
        Ok(decls)
    }

    /// 前进到下一个 token
    fn advance(&mut self) -> Result<(), ParseError> {
        self.current = self.lexer.next_token()?;
        Ok(())
    }

    /// 跳过换行符
    fn skip_newlines(&mut self) {
        while self.current == Token::NewLine {
            let _ = self.advance();
        }
    }

    /// 期望特定 token
    fn expect(&mut self, token: Token) -> Result<(), ParseError> {
        if std::mem::discriminant(&self.current) == std::mem::discriminant(&token) {
            self.advance()
        } else {
            Err(ParseError::UnexpectedToken {
                expected: format!("{:?}", token),
                found: format!("{:?}", self.current),
                pos: Position { line: self.lexer.line, column: self.lexer.column },
            })
        }
    }

    /// 解析声明
    fn parse_decl(&mut self) -> Result<Decl, ParseError> {
        match &self.current {
            Token::Let => self.parse_let_decl(),
            Token::Fn => self.parse_fun_decl(),
            Token::Type => self.parse_type_alias(),
            _ => Err(ParseError::InvalidSyntax {
                message: format!("Expected declaration, found {:?}", self.current),
                pos: Position { line: self.lexer.line, column: self.lexer.column },
            }),
        }
    }

    /// 解析 let 声明
    fn parse_let_decl(&mut self) -> Result<Decl, ParseError> {
        self.expect(Token::Let)?;
        
        let name = match &self.current {
            Token::Ident(n) => {
                let n = n.clone();
                self.advance()?;
                n
            }
            _ => return Err(ParseError::InvalidSyntax {
                message: "Expected identifier after 'let'".to_string(),
                pos: Position { line: self.lexer.line, column: self.lexer.column },
            }),
        };

        let ty = if self.current == Token::Colon {
            self.advance()?;
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect(Token::Assign)?;
        let value = self.parse_expr()?;

        Ok(Decl::Let { name, ty, value })
    }

    /// 解析函数声明
    fn parse_fun_decl(&mut self) -> Result<Decl, ParseError> {
        self.expect(Token::Fn)?;
        
        let name = match &self.current {
            Token::Ident(n) => {
                let n = n.clone();
                self.advance()?;
                n
            }
            _ => return Err(ParseError::InvalidSyntax {
                message: "Expected function name".to_string(),
                pos: Position { line: self.lexer.line, column: self.lexer.column },
            }),
        };

        // 泛型参数（简化处理，暂不支持）
        let generics = Vec::new();

        self.expect(Token::LParen)?;
        let params = self.parse_params()?;
        self.expect(Token::RParen)?;

        let ret_type = if self.current == Token::Arrow {
            self.advance()?;
            self.parse_type()?
        } else {
            Type::Unit
        };

        let body = self.parse_expr()?;

        Ok(Decl::Fun { name, generics, params, ret_type, body })
    }

    /// 解析参数列表
    fn parse_params(&mut self) -> Result<Vec<(String, Type)>, ParseError> {
        let mut params = Vec::new();
        
        while self.current != Token::RParen {
            let name = match &self.current {
                Token::Ident(n) => {
                    let n = n.clone();
                    self.advance()?;
                    n
                }
                _ => break,
            };

            self.expect(Token::Colon)?;
            let ty = self.parse_type()?;
            params.push((name, ty));

            if self.current == Token::Comma {
                self.advance()?;
            }
        }

        Ok(params)
    }

    /// 解析类型别名
    fn parse_type_alias(&mut self) -> Result<Decl, ParseError> {
        self.expect(Token::Type)?;
        
        let name = match &self.current {
            Token::Ident(n) => {
                let n = n.clone();
                self.advance()?;
                n
            }
            _ => return Err(ParseError::InvalidSyntax {
                message: "Expected type name".to_string(),
                pos: Position { line: self.lexer.line, column: self.lexer.column },
            }),
        };

        self.expect(Token::Assign)?;
        let ty = self.parse_type()?;

        Ok(Decl::TypeAlias { name, ty })
    }

    /// 解析类型
    fn parse_type(&mut self) -> Result<Type, ParseError> {
        let base = match &self.current {
            Token::TInt => { self.advance()?; Type::Int }
            Token::TBool => { self.advance()?; Type::Bool }
            Token::TString => { self.advance()?; Type::String }
            Token::TUnit => { self.advance()?; Type::Unit }
            Token::Ident(name) => {
                let name = name.clone();
                self.advance()?;
                Type::Var(name)
            }
            Token::LParen => {
                self.advance()?;
                // 函数类型: (T1, T2, ...) -> Ret
                let mut params = Vec::new();
                while self.current != Token::RParen {
                    params.push(self.parse_type()?);
                    if self.current == Token::Comma {
                        self.advance()?;
                    }
                }
                self.expect(Token::RParen)?;
                
                if self.current == Token::Arrow {
                    self.advance()?;
                    let ret = self.parse_type()?;
                    Type::Fun { params, ret: Box::new(ret) }
                } else {
                    // 元组类型
                    Type::Tuple(params)
                }
            }
            Token::LBracket => {
                self.advance()?;
                let elem = self.parse_type()?;
                self.expect(Token::RBracket)?;
                Type::Array(Box::new(elem))
            }
            _ => return Err(ParseError::InvalidSyntax {
                message: format!("Expected type, found {:?}", self.current),
                pos: Position { line: self.lexer.line, column: self.lexer.column },
            }),
        };

        Ok(base)
    }

    /// 解析表达式
    fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_or_expr()
    }

    /// 解析或表达式
    fn parse_or_expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_and_expr()?;
        
        while self.current == Token::Or {
            self.advance()?;
            let right = self.parse_and_expr()?;
            left = Expr::BinOp {
                op: BinOperator::Or,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        
        Ok(left)
    }

    /// 解析与表达式
    fn parse_and_expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_eq_expr()?;
        
        while self.current == Token::And {
            self.advance()?;
            let right = self.parse_eq_expr()?;
            left = Expr::BinOp {
                op: BinOperator::And,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        
        Ok(left)
    }

    /// 解析相等表达式
    fn parse_eq_expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_rel_expr()?;
        
        loop {
            let op = match self.current {
                Token::Eq => BinOperator::Eq,
                Token::Ne => BinOperator::Ne,
                _ => break,
            };
            self.advance()?;
            let right = self.parse_rel_expr()?;
            left = Expr::BinOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        
        Ok(left)
    }

    /// 解析关系表达式
    fn parse_rel_expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_add_expr()?;
        
        loop {
            let op = match self.current {
                Token::Lt => BinOperator::Lt,
                Token::Le => BinOperator::Le,
                Token::Gt => BinOperator::Gt,
                Token::Ge => BinOperator::Ge,
                _ => break,
            };
            self.advance()?;
            let right = self.parse_add_expr()?;
            left = Expr::BinOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        
        Ok(left)
    }

    /// 解析加法表达式
    fn parse_add_expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_mul_expr()?;
        
        loop {
            let op = match self.current {
                Token::Plus => BinOperator::Add,
                Token::Minus => BinOperator::Sub,
                _ => break,
            };
            self.advance()?;
            let right = self.parse_mul_expr()?;
            left = Expr::BinOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        
        Ok(left)
    }

    /// 解析乘法表达式
    fn parse_mul_expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_unary_expr()?;
        
        loop {
            let op = match self.current {
                Token::Star => BinOperator::Mul,
                Token::Slash => BinOperator::Div,
                Token::Percent => BinOperator::Mod,
                _ => break,
            };
            self.advance()?;
            let right = self.parse_unary_expr()?;
            left = Expr::BinOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        
        Ok(left)
    }

    /// 解析一元表达式
    fn parse_unary_expr(&mut self) -> Result<Expr, ParseError> {
        match self.current {
            Token::Minus => {
                self.advance()?;
                let operand = self.parse_unary_expr()?;
                Ok(Expr::UnOp { op: UnOperator::Neg, operand: Box::new(operand) })
            }
            Token::Not => {
                self.advance()?;
                let operand = self.parse_unary_expr()?;
                Ok(Expr::UnOp { op: UnOperator::Not, operand: Box::new(operand) })
            }
            _ => self.parse_app_expr(),
        }
    }

    /// 解析函数应用表达式
    fn parse_app_expr(&mut self) -> Result<Expr, ParseError> {
        let mut func = self.parse_primary_expr()?;
        
        // 处理函数调用
        while self.current == Token::LParen {
            self.advance()?;
            let args = self.parse_args()?;
            self.expect(Token::RParen)?;
            func = Expr::Call { func: Box::new(func), args };
        }
        
        Ok(func)
    }

    /// 解析参数列表
    fn parse_args(&mut self) -> Result<Vec<Expr>, ParseError> {
        let mut args = Vec::new();
        
        while self.current != Token::RParen {
            args.push(self.parse_expr()?);
            if self.current == Token::Comma {
                self.advance()?;
            } else {
                break;
            }
        }
        
        Ok(args)
    }

    /// 解析基本表达式
    fn parse_primary_expr(&mut self) -> Result<Expr, ParseError> {
        match &self.current {
            Token::Int(n) => {
                let n = *n;
                self.advance()?;
                Ok(Expr::Int(n))
            }
            Token::True => {
                self.advance()?;
                Ok(Expr::Bool(true))
            }
            Token::False => {
                self.advance()?;
                Ok(Expr::Bool(false))
            }
            Token::String(s) => {
                let s = s.clone();
                self.advance()?;
                Ok(Expr::String(s))
            }
            Token::Ident(name) => {
                let name = name.clone();
                self.advance()?;
                Ok(Expr::Var(name))
            }
            Token::LParen => {
                self.advance()?;
                if self.current == Token::RParen {
                    self.advance()?;
                    Ok(Expr::Unit)
                } else {
                    let expr = self.parse_expr()?;
                    self.expect(Token::RParen)?;
                    Ok(expr)
                }
            }
            Token::LBrace => self.parse_block(),
            Token::If => self.parse_if_expr(),
            _ => Err(ParseError::InvalidSyntax {
                message: format!("Unexpected token: {:?}", self.current),
                pos: Position { line: self.lexer.line, column: self.lexer.column },
            }),
        }
    }

    /// 解析代码块
    fn parse_block(&mut self) -> Result<Expr, ParseError> {
        self.expect(Token::LBrace)?;
        self.skip_newlines();
        
        let mut exprs = Vec::new();
        while self.current != Token::RBrace {
            exprs.push(self.parse_expr()?);
            self.skip_newlines();
            if self.current == Token::Semicolon {
                self.advance()?;
                self.skip_newlines();
            }
        }
        
        self.expect(Token::RBrace)?;
        Ok(Expr::Block(exprs))
    }

    /// 解析条件表达式
    fn parse_if_expr(&mut self) -> Result<Expr, ParseError> {
        self.expect(Token::If)?;
        let cond = self.parse_expr()?;
        
        let then_branch = if self.current == Token::LBrace {
            self.parse_block()?
        } else {
            self.parse_expr()?
        };
        
        let else_branch = if self.current == Token::Else {
            self.advance()?;
            if self.current == Token::If {
                self.parse_if_expr()?
            } else if self.current == Token::LBrace {
                self.parse_block()?
            } else {
                self.parse_expr()?
            }
        } else {
            Expr::Unit
        };
        
        Ok(Expr::If {
            cond: Box::new(cond),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        })
    }
}

/// 便捷解析函数
pub fn parse(input: &str) -> Result<Program, ParseError> {
    let mut parser = Parser::new(input)?;
    parser.parse_program()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_int() {
        let program = parse("let x = 42").unwrap();
        assert_eq!(program.len(), 1);
        
        if let Decl::Let { name, value, .. } = &program[0] {
            assert_eq!(name, "x");
            assert!(matches!(value, Expr::Int(42)));
        } else {
            panic!("Expected let declaration");
        }
    }

    #[test]
    fn test_parse_binop() {
        let program = parse("let sum = 1 + 2").unwrap();
        assert_eq!(program.len(), 1);
    }

    #[test]
    fn test_parse_function() {
        let program = parse("fn add(x: Int, y: Int) -> Int { x + y }").unwrap();
        assert_eq!(program.len(), 1);
        
        if let Decl::Fun { name, params, ret_type, .. } = &program[0] {
            assert_eq!(name, "add");
            assert_eq!(params.len(), 2);
            assert_eq!(ret_type, &Type::Int);
        } else {
            panic!("Expected function declaration");
        }
    }

    #[test]
    fn test_parse_if() {
        let program = parse("let max = if x > y then x else y").unwrap();
        assert_eq!(program.len(), 1);
    }
}
