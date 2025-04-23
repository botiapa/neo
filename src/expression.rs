use tracing::{instrument, trace};

use crate::tokenizer::Token;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum UnaryOp {
    Plus,
    Minus,
    Negate,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BinaryOp {
    Add,
    Sub,
    Mult,
    Div,
    GreaterThan,
    GreaterOrEqualThan,
    LessThan,
    LessOrEqualThan,
    Equal,
}

pub(crate) type Path = Vec<String>;
pub(crate) type VarType = (String, Path);
pub(crate) type ArgName = String;
pub(crate) type Args = Vec<(ArgName, Option<VarType>)>;

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct EnumVariant {
    pub(crate) enum_name: String,
    pub(crate) variant_name: String,
    pub(crate) values: Vec<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct EnumDeclaration {
    pub(crate) name: String,
    pub(crate) variants: Vec<(String, Option<Vec<String>>)>,
}

pub(crate) type Id = String;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Expr {
    NumLit(i32),
    StringLit(String),
    BoolLit(bool),
    Identifier(Id, Path),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    FunctionCall(Id, Vec<Expr>),
    Block(Vec<Expr>),
    Assignment(Id, Box<Expr>, Option<VarType>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    While(Box<Expr>, Box<Expr>),
    FunctionDeclaration(String, Args, Box<Expr>),
    EnumDeclaration(EnumDeclaration),
    EnumVariant(EnumVariant),
    Is(Id, Box<Expr>),
    NoOp,
}

pub(crate) mod delimited;
pub(crate) mod helpers;

#[derive(Debug)]
pub(crate) struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    pub(crate) fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, pos: 0 }
    }

    pub(crate) fn parse(&mut self) -> Result<Option<Expr>, String> {
        let mut top_block = Vec::new();
        while let Some(block) = self.parse_block()? {
            top_block.push(block);
            trace!(
                "Pushing top block: {:?}, top_block: {:?}, remaining tokens: {:?}",
                top_block.last().unwrap(),
                top_block,
                self.remaining_tokens()
            );
        }

        if top_block.len() > 1 {
            Ok(Some(Expr::Block(top_block)))
        } else {
            Ok(top_block.pop())
        }
    }

    fn peek(&self) -> Option<Token> {
        self.tokens.get(self.pos).cloned()
    }

    fn consume(&mut self) -> Option<Token> {
        let token = self.peek();
        if token.is_some() {
            self.pos += 1;
        }
        token
    }

    fn remaining_tokens(&self) -> Vec<Token> {
        self.tokens.iter().skip(self.pos).cloned().collect()
    }

    fn parse_block(&mut self) -> Result<Option<Expr>, String> {
        let mut block = Vec::new();
        let start = self.pos;
        if let Some(Token::OpenCurly) = self.consume() {
            trace!("Parsing block, tokens: {:?}", self.remaining_tokens());

            while let Some(token) = self.peek() {
                match token {
                    Token::CloseCurly => {
                        self.consume();
                        break;
                    }
                    _ => {
                        if let Some(expr) = self.parse_block()? {
                            if let Some(Token::SemiColon) = self.peek() {
                                self.consume();
                            }
                            trace!(
                                "Parsed expr, adding to block: {:?} remaining tokens: {:?}",
                                expr,
                                self.remaining_tokens()
                            );
                            block.push(expr);
                        }
                    }
                }
            }
            trace!(
                "Parsed block: {:?}, remaining tokens: {:?}",
                block,
                self.remaining_tokens()
            );
            return Ok(Some(Expr::Block(block)));
        }
        trace!("Failed to parse block, parsing expr");
        self.pos = start;
        let expr = self.parse_expr()?;
        if let Some(Token::SemiColon) = self.peek() {
            self.consume();
        }
        Ok(expr)
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_expr(&mut self) -> Result<Option<Expr>, String> {
        let expr = match self.parse_while() {
            Ok(Some(expr)) => expr,
            expr @ _ => return expr,
        };

        trace!("Parsed expr: {:?}", expr);
        Ok(Some(expr))
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_while(&mut self) -> Result<Option<Expr>, String> {
        let start = self.pos;
        if let Some(Token::While) = self.consume() {
            let cond = self
                .parse_block()?
                .ok_or(format!("Expected expression after 'while'"))?;
            trace!("Parsed cond: {:?}", cond);
            let block = self
                .parse_block()?
                .ok_or(format!("Expected expression after 'condition'"))?;
            trace!("Parsed block: {:?}", block);
            return Ok(Some(Expr::While(Box::new(cond), Box::new(block))));
        }
        self.pos = start;
        self.parse_if()
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_if(&mut self) -> Result<Option<Expr>, String> {
        let start = self.pos;
        if let Some(Token::If) = self.consume() {
            let cond = self
                .parse_block()?
                .ok_or(format!("Expected expression after 'if'"))?;
            trace!("Parsed cond: {:?}", cond);
            let then = self
                .parse_block()?
                .ok_or(format!("Expected expression after 'condition'"))?;
            trace!("Parsed then: {:?}", then);
            if let Some(Token::Else) = self.peek() {
                self.consume();
                let else_block = self
                    .parse_block()?
                    .ok_or(format!("Expected expression after 'else'"))?;

                return Ok(Some(Expr::If(
                    Box::new(cond),
                    Box::new(then),
                    Some(Box::new(else_block)),
                )));
            } else {
                return Ok(Some(Expr::If(Box::new(cond), Box::new(then), None)));
            }
        }
        self.pos = start;
        self.parse_enum_declaration()
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_enum_declaration(&mut self) -> Result<Option<Expr>, String> {
        let start = self.pos;
        if let Some(Token::Enum) = self.consume() {
            let name = match self.consume() {
                Some(Token::Ident(name)) => name,
                _ => return Err("Expected enum name".to_string()),
            };

            if let Some(Token::OpenCurly) = self.consume() {
            } else {
                return Err("Expected '{' after enum name".to_string());
            }

            let mut variants = Vec::new();
            loop {
                let variant = match self.consume() {
                    Some(Token::Ident(variant)) => variant,
                    _ => break,
                };
                let mut variant_fields = None;
                if let Some(Token::LeftPar) = self.peek() {
                    self.consume();
                    let mut fields = Vec::new();
                    while let Some(Token::Ident(field)) = self.peek() {
                        self.consume();
                        fields.push(field);
                        if let Some(Token::Comma) = self.peek() {
                            self.consume();
                        } else {
                            if self.consume() != Some(Token::RightPar) {
                                return Err("Expected ')' after last field".to_string());
                            }
                        }
                    }
                    variant_fields = Some(fields);
                }
                trace!("Parsed variant: {:?}", variant);
                variants.push((variant, variant_fields));
                if let Some(Token::Comma) = self.peek() {
                    self.consume();
                } else {
                    if self.consume() != Some(Token::CloseCurly) {
                        return Err("Expected '}' after enum variants".to_string());
                    }
                    break;
                }
            }

            trace!("Parsed enum declaration({}): {:?}", name, variants);
            return Ok(Some(Expr::EnumDeclaration(EnumDeclaration {
                name,
                variants,
            })));
        }
        self.pos = start;
        self.parse_function_declaration()
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_function_declaration(&mut self) -> Result<Option<Expr>, String> {
        let start = self.pos;
        if let Some(Token::Function) = self.consume() {
            trace!("Parsed function declaration");
            let name = match self.consume() {
                Some(Token::Ident(name)) => name,
                _ => return Err("Expected function name".to_string()),
            };

            trace!("Parsed function name: {:?}", name);
            if let Some(Token::LeftPar) = self.consume() {
            } else {
                return Err("Expected '(' after function name".to_string());
            }

            // parse args
            let mut args = Vec::new();
            trace!("Parsing function args");
            while self.peek() != Some(Token::RightPar) {
                trace!(
                    "Parsing function arg, remaining tokens: {:?}",
                    self.remaining_tokens()
                );
                if let Some(Token::Ident(id)) = self.peek() {
                    self.consume();
                    if let Some(Token::Colon) = self.peek() {
                        self.consume();
                        let var_type = match self.parse_expr() {
                            Ok(Some(Expr::Identifier(var_type, path))) => (var_type, path),
                            _ => return Err("Expected type after ':'".to_string()),
                        };
                        args.push((id, Some(var_type)));
                    } else {
                        args.push((id, None));
                    }
                }
                if let Some(Token::Comma) = self.peek() {
                    self.consume();
                } else {
                    if let Some(Token::RightPar) = self.peek() {
                    } else {
                        return Err("Expected ')' after last arg".to_string());
                    }
                }
            }
            self.consume();
            let body = self.parse_block()?;
            if let Some(body) = body {
                return Ok(Some(Expr::FunctionDeclaration(name, args, Box::new(body))));
            } else {
                return Err("Expected expression after ')'".to_string());
            }
        }
        self.pos = start;
        self.parse_assignment()
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_assignment(&mut self) -> Result<Option<Expr>, String> {
        let start = self.pos;
        let left = match self.parse_is() {
            Ok(Some(expr)) => expr,
            left @ _ => return left,
        };
        trace!("Parsed: {:?}", left);

        let var_type = match self.peek() {
            Some(Token::Colon) => {
                self.consume();
                let right = match self.parse_is() {
                    Ok(Some(Expr::Identifier(id, path))) => (id, path),
                    expr @ _ => return Err(format!("Expected type after ':', got {:?}", expr)),
                };
                Some(right)
            }
            _ => None,
        };

        if let Some(Token::Assign) = self.consume() {
            if let Expr::Identifier(id, path) = left {
                if path.len() > 0 {
                    return Err(format!("Expected type after ':', got {:?}", path));
                }

                let right = match self.parse_is() {
                    Ok(Some(expr)) => expr,
                    expr @ _ => return expr,
                };
                return Ok(Some(Expr::Assignment(id, Box::new(right), var_type)));
            } else {
                return Err(format!("Invalid left-hand side of assignment: {:?}", left));
            }
        }

        if let Some(var_type) = var_type {
            return Err(format!("Expected assignment after ':', got {:?}", var_type));
        }

        self.pos = start;
        self.parse_is()
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_is(&mut self) -> Result<Option<Expr>, String> {
        let start = self.pos;
        let left = match self.parse_comp() {
            Ok(Some(expr)) => expr,
            left @ _ => return left,
        };

        if let Some(Token::Is) = self.consume() {
            let right = match self.parse_expr() {
                Ok(Some(expr)) => expr,
                expr @ _ => return expr,
            };
            if let Expr::Identifier(iden, _) = left {
                return Ok(Some(Expr::Is(iden, Box::new(right))));
            } else {
                return Err(format!("Expected identifier after 'is', got {:?}", left));
            }
        }

        self.pos = start;
        self.parse_comp()
    }

    #[inline]
    fn peek_comp(&self) -> Option<Token> {
        match self.peek() {
            Some(Token::GreaterThan) => Some(Token::GreaterThan),
            Some(Token::GreaterOrEqualThan) => Some(Token::GreaterOrEqualThan),
            Some(Token::LessThan) => Some(Token::LessThan),
            Some(Token::LessOrEqualThan) => Some(Token::LessOrEqualThan),
            Some(Token::Equal) => Some(Token::Equal),
            _ => None,
        }
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_comp(&mut self) -> Result<Option<Expr>, String> {
        let mut left = match self.parse_add_sub() {
            Ok(Some(expr)) => expr,
            left @ _ => return left,
        };
        trace!("Parsed: {:?}", left);

        if let Some(token) = self.peek_comp() {
            self.consume();
            let right = match self.parse_add_sub() {
                Ok(Some(expr)) => expr,
                expr @ _ => return expr,
            };

            let op = match token {
                Token::GreaterThan => BinaryOp::GreaterThan,
                Token::GreaterOrEqualThan => BinaryOp::GreaterOrEqualThan,
                Token::LessThan => BinaryOp::LessThan,
                Token::LessOrEqualThan => BinaryOp::LessOrEqualThan,
                Token::Equal => BinaryOp::Equal,
                _ => unreachable!(),
            };
            left = Expr::Binary(op, Box::new(left), Box::new(right));
        }
        Ok(Some(left))
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_add_sub(&mut self) -> Result<Option<Expr>, String> {
        let mut left = match self.parse_mult_div() {
            Ok(Some(expr)) => expr,
            left @ _ => return left,
        };
        trace!("Parsed: {:?}", left);

        while let Some(token) = self.peek() {
            match token {
                Token::Plus | Token::Minus => {
                    self.consume();
                    let right = match self.parse_mult_div() {
                        Ok(Some(expr)) => expr,
                        expr @ _ => return expr,
                    };

                    let op = match token {
                        Token::Plus => BinaryOp::Add,
                        Token::Minus => BinaryOp::Sub,
                        _ => unreachable!(),
                    };
                    left = Expr::Binary(op, Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }
        Ok(Some(left))
    }

    fn parse_mult_div(&mut self) -> Result<Option<Expr>, String> {
        let mut left = match self.parse_primary() {
            Ok(Some(expr)) => expr,
            left @ _ => return left,
        };

        while let Some(token) = self.peek() {
            match token {
                Token::Mult | Token::Div => {
                    self.consume();
                    let right = match self.parse_primary() {
                        Ok(Some(expr)) => expr,
                        expr @ _ => return expr,
                    };

                    let op = match token {
                        Token::Mult => BinaryOp::Mult,
                        Token::Div => BinaryOp::Div,
                        _ => unreachable!(),
                    };
                    left = Expr::Binary(op, Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }
        Ok(Some(left))
    }

    fn parse_primary(&mut self) -> Result<Option<Expr>, String> {
        if let Ok(Some(expr)) = self.parse_function_call() {
            return Ok(Some(expr));
        }

        if let Ok(Some(expr)) = self.parse_unary() {
            return Ok(Some(expr));
        }

        if let Ok(Some(expr)) = self.parse_paren() {
            return Ok(Some(expr));
        }

        let expr = match self.consume() {
            Some(expr) => expr,
            None => return Ok(None),
        };

        let expr = match expr {
            Token::NumLiteral(n) => Expr::NumLit(n),
            Token::StringLiteral(s) => Expr::StringLit(s),
            Token::BoolLiteral(b) => Expr::BoolLit(b),
            Token::Ident(id) => {
                let mut path = vec![id];
                while let Some(Token::DoubleColon) = self.peek() {
                    self.consume();
                    if let Some(Token::Ident(id)) = self.consume() {
                        path.push(id);
                    } else {
                        return Err("Expected identifier after '::'".to_string());
                    }
                }
                Expr::Identifier(path.pop().unwrap(), path)
            }
            token => return Err(format!("Unexpected token: {:?}", token)),
        };
        Ok(Some(expr))
    }

    fn parse_function_call(&mut self) -> Result<Option<Expr>, String> {
        let start = self.pos;
        if let Some(Token::Ident(fn_name)) = self.consume() {
            if let Some(Token::LeftPar) = self.consume() {
                let mut args = Vec::new();
                while self.peek() != Some(Token::RightPar) {
                    let arg = match self.parse_expr() {
                        Ok(Some(expr)) => expr,
                        expr @ _ => return expr,
                    };

                    args.push(arg);
                    if let Some(Token::Comma) = self.peek() {
                        self.consume();
                    }
                }
                if let Some(Token::RightPar) = self.consume() {
                    return Ok(Some(Expr::FunctionCall(fn_name, args)));
                }
                return Err("Expected ')' after function arguments".to_string());
            }
        }
        self.pos = start;
        Ok(None)
    }

    fn parse_unary(&mut self) -> Result<Option<Expr>, String> {
        let expr = match self.peek() {
            Some(expr) => expr,
            None => return Ok(None),
        };

        match expr {
            Token::Plus => {
                self.consume();
                let expr = match self.parse_primary() {
                    Ok(Some(expr)) => expr,
                    expr @ _ => return expr,
                };
                Ok(Some(Expr::Unary(UnaryOp::Plus, Box::new(expr))))
            }
            Token::Minus => {
                self.consume();
                let expr = match self.parse_primary() {
                    Ok(Some(expr)) => expr,
                    expr @ _ => return expr,
                };
                Ok(Some(Expr::Unary(UnaryOp::Minus, Box::new(expr))))
            }
            Token::Negate => {
                self.consume();
                let expr = match self.parse_primary() {
                    Ok(Some(expr)) => expr,
                    expr @ _ => return expr,
                };
                Ok(Some(Expr::Unary(UnaryOp::Negate, Box::new(expr))))
            }
            _ => Ok(None),
        }
    }

    fn parse_paren(&mut self) -> Result<Option<Expr>, String> {
        let expr = match self.peek() {
            Some(expr) => expr,
            None => return Ok(None),
        };

        match expr {
            Token::LeftPar => {
                self.consume();

                if let Some(Token::RightPar) = self.peek() {
                    self.consume();
                    return Ok(None);
                }

                let expr = self.parse_expr();
                if self.consume() != Some(Token::RightPar) {
                    panic!("Expected ')'");
                }
                expr
            }
            _ => Ok(None),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::helpers::*;
    use crate::expression::{BinaryOp, UnaryOp};

    use super::{Parser, Token};

    #[test]
    fn parse_single_expr() {
        let mut parser = Parser::new(vec![Token::NumLiteral(42)]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(expr, num_lit(42));
    }

    #[test]
    fn parse_add() {
        let mut parser = Parser::new(vec![
            Token::NumLiteral(1),
            Token::Plus,
            Token::NumLiteral(2),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(expr, binary(BinaryOp::Add, num_lit(1), num_lit(2)));
    }

    #[test]
    fn parse_block() {
        let mut parser = Parser::new(vec![
            Token::OpenCurly,
            Token::NumLiteral(1),
            Token::SemiColon,
            Token::NumLiteral(2),
            Token::SemiColon,
            Token::NumLiteral(3),
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(expr, block(&[num_lit(1), num_lit(2), num_lit(3)]));
    }

    #[test]
    fn parse_assignment() {
        let mut parser = Parser::new(vec![
            Token::Ident("a".to_string()),
            Token::Assign,
            Token::NumLiteral(42),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(expr, assignment("a".to_string(), num_lit(42)));
    }

    #[test]
    fn parse_assignment_usage() {
        let mut parser = Parser::new(vec![
            Token::Ident("a".to_string()),
            Token::Assign,
            Token::NumLiteral(42),
            Token::SemiColon,
            Token::Ident("a".to_string()),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            block(&[assignment("a".to_string(), num_lit(42)), iden("a")])
        );
    }

    #[test]
    fn parse_eq() {
        let mut parser = Parser::new(vec![
            Token::NumLiteral(1),
            Token::Equal,
            Token::NumLiteral(2),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(expr, binary(BinaryOp::Equal, num_lit(1), num_lit(2)));
    }

    #[test]
    fn comp_precedence() {
        let mut parser = Parser::new(vec![
            Token::NumLiteral(1),
            Token::Plus,
            Token::NumLiteral(1),
            Token::Equal,
            Token::NumLiteral(1),
            Token::Plus,
            Token::NumLiteral(1),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            binary(
                BinaryOp::Equal,
                binary(BinaryOp::Add, num_lit(1), num_lit(1)),
                binary(BinaryOp::Add, num_lit(1), num_lit(1))
            )
        );
    }

    #[test]
    fn fail_const_assignment() {
        let mut parser = Parser::new(vec![
            Token::NumLiteral(42),
            Token::Assign,
            Token::NumLiteral(42),
        ]);
        let expr = parser.parse();
        assert!(expr.is_err());
    }

    #[test]
    fn fail_compl_assignment() {
        //a=1==1=b
        let mut parser = Parser::new(vec![
            Token::NumLiteral(1),
            Token::Equal,
            Token::NumLiteral(1),
            Token::Assign,
            Token::Ident("b".to_string()),
        ]);
        let expr = parser.parse();
        assert!(expr.is_err());
    }

    #[test]
    fn simple_if_expr() {
        // if a > b {a}
        let mut parser = Parser::new(vec![
            Token::If,
            Token::Ident("a".to_string()),
            Token::GreaterThan,
            Token::Ident("b".to_string()),
            Token::OpenCurly,
            Token::Ident("a".to_string()),
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            if_expr(
                binary(BinaryOp::GreaterThan, iden("a"), iden("b")),
                block(&[iden("a")]),
                None
            )
        );
    }

    #[test]
    fn if_else_expr() {
        // if a > b {a} else {b}
        let mut parser = Parser::new(vec![
            Token::If,
            Token::Ident("a".to_string()),
            Token::GreaterThan,
            Token::Ident("b".to_string()),
            Token::OpenCurly,
            Token::Ident("a".to_string()),
            Token::CloseCurly,
            Token::Else,
            Token::OpenCurly,
            Token::Ident("b".to_string()),
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            if_expr(
                binary(BinaryOp::GreaterThan, iden("a"), iden("b")),
                block(&[iden("a")]),
                Some(block(&[iden("b")]))
            )
        );
    }

    #[test]
    fn if_else_if() {
        // if a > b { 42; } else if a < b { 69; } else { 420; }
        let mut parser = Parser::new(vec![
            Token::If,
            Token::Ident("a".to_string()),
            Token::GreaterThan,
            Token::Ident("b".to_string()),
            Token::OpenCurly,
            Token::NumLiteral(42),
            Token::SemiColon,
            Token::CloseCurly,
            Token::Else,
            Token::If,
            Token::Ident("a".to_string()),
            Token::LessThan,
            Token::Ident("b".to_string()),
            Token::OpenCurly,
            Token::NumLiteral(69),
            Token::SemiColon,
            Token::CloseCurly,
            Token::Else,
            Token::OpenCurly,
            Token::NumLiteral(420),
            Token::SemiColon,
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            if_expr(
                binary(BinaryOp::GreaterThan, iden("a"), iden("b")),
                block(&[num_lit(42)]),
                Some(if_expr(
                    binary(BinaryOp::LessThan, iden("a"), iden("b")),
                    block(&[num_lit(69)]),
                    Some(block(&[num_lit(420)]))
                ))
            )
        )
    }

    #[test]
    fn complex_if() {
        // if a > b { a; b; }
        let mut parser = Parser::new(vec![
            Token::If,
            Token::Ident("a".to_string()),
            Token::GreaterThan,
            Token::Ident("b".to_string()),
            Token::OpenCurly,
            Token::Ident("a".to_string()),
            Token::SemiColon,
            Token::Ident("b".to_string()),
            Token::SemiColon,
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            if_expr(
                binary(BinaryOp::GreaterThan, iden("a"), iden("b")),
                block(&[iden("a"), iden("b")]),
                None
            )
        );
    }

    #[test]
    fn empty_block() {
        let mut parser = Parser::new(vec![Token::OpenCurly, Token::CloseCurly]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(expr, block(&[]));
    }

    #[test]
    fn ab_block() {
        let mut parser = Parser::new(vec![
            Token::OpenCurly,
            Token::Ident("a".to_string()),
            Token::SemiColon,
            Token::Ident("b".to_string()),
            Token::SemiColon,
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(expr, block(&[iden("a"), iden("b")]));
    }

    #[test]
    fn simple_while_expr() {
        // while a > b { a; }
        let mut parser = Parser::new(vec![
            Token::While,
            Token::Ident("a".to_string()),
            Token::GreaterThan,
            Token::Ident("b".to_string()),
            Token::OpenCurly,
            Token::Ident("a".to_string()),
            Token::SemiColon,
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            while_expr(
                binary(BinaryOp::GreaterThan, iden("a"), iden("b")),
                block(&[iden("a")])
            )
        )
    }

    #[test]
    fn complex_while() {
        // while a > b { a; b; }
        let mut parser = Parser::new(vec![
            Token::While,
            Token::Ident("a".to_string()),
            Token::GreaterThan,
            Token::Ident("b".to_string()),
            Token::OpenCurly,
            Token::Ident("a".to_string()),
            Token::SemiColon,
            Token::Ident("b".to_string()),
            Token::SemiColon,
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            while_expr(
                binary(BinaryOp::GreaterThan, iden("a"), iden("b")),
                block(&[iden("a"), iden("b")])
            )
        )
    }

    #[test]
    fn negate() {
        let mut parser = Parser::new(vec![Token::Negate, Token::BoolLiteral(true)]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(expr, unary(UnaryOp::Negate, bool_lit(true)));
    }

    #[test]
    fn typed_assignment_invalid() {
        let mut parser = Parser::new(vec![
            Token::Ident("a".to_string()),
            Token::Colon,
            Token::Ident("int".to_string()),
        ]);
        let expr = parser.parse();
        assert!(expr.is_err()); // no null values allowed
    }

    #[test]
    fn typed_assignment_valid() {
        let mut parser = Parser::new(vec![
            Token::Ident("a".to_string()),
            Token::Colon,
            Token::Ident("int".to_string()),
            Token::Assign,
            Token::NumLiteral(42),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            assignment_typed("a".to_string(), num_lit(42), ("int".to_string(), vec![]))
        );
    }

    #[test]
    fn simple_function_declaration() {
        let mut parser = Parser::new(vec![
            Token::Function,
            Token::Ident("a".to_string()),
            Token::LeftPar,
            Token::Ident("b".to_string()),
            Token::Colon,
            Token::Ident("int".to_string()),
            Token::RightPar,
            Token::OpenCurly,
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            function_declaration(
                "a".to_string(),
                vec![("b".to_string(), Some(("int".to_string(), vec![])))],
                block(&[])
            )
        );
    }

    #[test]
    fn function_declaration_noblock() {
        let mut parser = Parser::new(vec![
            Token::Function,
            Token::Ident("a".to_string()),
            Token::LeftPar,
            Token::RightPar,
            Token::Ident("a".to_string()),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            function_declaration("a".to_string(), vec![], iden("a"))
        );
    }

    #[test]
    fn function_declaration_multiple_args() {
        let mut parser = Parser::new(vec![
            Token::Function,
            Token::Ident("a".to_string()),
            Token::LeftPar,
            Token::Ident("b".to_string()),
            Token::Colon,
            Token::Ident("int".to_string()),
            Token::Comma,
            Token::Ident("c".to_string()),
            Token::RightPar,
            Token::OpenCurly,
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            function_declaration(
                "a".to_string(),
                vec![
                    ("b".to_string(), Some(("int".to_string(), vec![]))),
                    ("c".to_string(), None)
                ],
                block(&[])
            )
        );
    }

    #[test]
    fn empty_enum_declaration() {
        let mut parser = Parser::new(vec![
            Token::Enum,
            Token::Ident("A".to_string()),
            Token::OpenCurly,
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(expr, enum_dec("A".to_string(), vec![]));
    }

    #[test]
    fn enum_declaration() {
        // enum A { B(int, int), C }
        let mut parser = Parser::new(vec![
            Token::Enum,
            Token::Ident("A".to_string()),
            Token::OpenCurly,
            Token::Ident("B".to_string()),
            Token::LeftPar,
            Token::Ident("int".to_string()),
            Token::Comma,
            Token::Ident("int".to_string()),
            Token::RightPar,
            Token::Comma,
            Token::Ident("C".to_string()),
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            enum_dec(
                "A".to_string(),
                vec![
                    (
                        "B".to_string(),
                        Some(vec!["int".to_string(), "int".to_string()])
                    ),
                    ("C".to_string(), None)
                ]
            )
        );
    }

    #[test]
    fn identifier_with_path() {
        // A::B::C
        let mut parser = Parser::new(vec![
            Token::Ident("A".to_string()),
            Token::DoubleColon,
            Token::Ident("B".to_string()),
            Token::DoubleColon,
            Token::Ident("C".to_string()),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            iden_with_path("C", vec!["A".to_string(), "B".to_string()])
        );
    }

    #[test]
    fn enum_declaration_and_usage() {
        let mut parser = Parser::new(vec![
            Token::Enum,
            Token::Ident("A".to_string()),
            Token::OpenCurly,
            Token::Ident("B".to_string()),
            Token::CloseCurly,
            Token::Ident("A".to_string()),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            block(&[
                enum_dec("A".to_string(), vec![("B".to_string(), None)]),
                iden("A"),
            ])
        );
    }

    #[test]
    fn fn_path_args() {
        // fn a(a: A::B) {}
        let mut parser = Parser::new(vec![
            Token::Function,
            Token::Ident("a".to_string()),
            Token::LeftPar,
            Token::Ident("a".to_string()),
            Token::Colon,
            Token::Ident("A".to_string()),
            Token::DoubleColon,
            Token::Ident("B".to_string()),
            Token::RightPar,
            Token::OpenCurly,
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            function_declaration(
                "a".to_string(),
                vec![(
                    "a".to_string(),
                    Some(("B".to_string(), vec!["A".to_string()]))
                )],
                block(&[])
            )
        );
    }

    #[test]
    fn assignment_with_path() {
        let mut parser = Parser::new(vec![
            Token::Ident("a".to_string()),
            Token::Colon,
            Token::Ident("A".to_string()),
            Token::DoubleColon,
            Token::Ident("B".to_string()),
            Token::Assign,
            Token::Ident("c".to_string()),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            assignment_typed(
                "a".to_string(),
                iden("c"),
                ("B".to_string(), vec!["A".to_string()])
            )
        );
    }

    #[test]
    fn test_is_expr() {
        // if a is A(n) { n; }
        let mut parser = Parser::new(vec![
            Token::If,
            Token::Ident("a".to_string()),
            Token::Is,
            Token::Ident("A".to_string()),
            Token::LeftPar,
            Token::Ident("n".to_string()),
            Token::RightPar,
            Token::OpenCurly,
            Token::Ident("n".to_string()),
            Token::SemiColon,
            Token::CloseCurly,
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            if_expr(
                is_expr("a", function_call("A".to_string(), vec![iden("n")])),
                block(&[iden("n")]),
                None
            )
        );
    }

    #[test]
    fn after_if_without_semi() {
        // if true {} b
        let mut parser = Parser::new(vec![
            Token::If,
            Token::BoolLiteral(true),
            Token::OpenCurly,
            Token::CloseCurly,
            Token::Ident("b".to_string()),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            block(&[if_expr(bool_lit(true), block(&[]), None), iden("b")])
        );
    }
}
