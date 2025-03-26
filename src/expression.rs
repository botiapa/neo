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

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Expr {
    NumLit(i32),
    StringLit(String),
    BoolLit(bool),
    Identifier(String),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    Function(Token, Vec<Expr>),
    Block(Vec<Expr>),
    Assignment(String, Box<Expr>, Option<String>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    While(Box<Expr>, Box<Expr>),
    NoOp,
}

#[allow(unused)]
pub(crate) mod helpers {
    use crate::tokenizer::Token;

    use super::{BinaryOp, Expr, UnaryOp};

    pub(crate) fn num_lit(n: i32) -> Expr {
        Expr::NumLit(n)
    }

    pub(crate) fn string_lit(s: String) -> Expr {
        Expr::StringLit(s)
    }

    pub(crate) fn bool_lit(b: bool) -> Expr {
        Expr::BoolLit(b)
    }

    pub(crate) fn iden(id: &str) -> Expr {
        Expr::Identifier(id.to_string())
    }

    pub(crate) fn unary(op: UnaryOp, expr: Expr) -> Expr {
        Expr::Unary(op, Box::new(expr))
    }

    pub(crate) fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
        Expr::Binary(op, Box::new(left), Box::new(right))
    }

    pub(crate) fn function(name: Token, args: Vec<Expr>) -> Expr {
        Expr::Function(name, args)
    }

    pub(crate) fn block(exprs: &[Expr]) -> Expr {
        Expr::Block(exprs.to_vec())
    }

    pub(crate) fn assignment(id: String, expr: Expr) -> Expr {
        Expr::Assignment(id, Box::new(expr), None)
    }

    pub(crate) fn assignment_typed(id: String, expr: Expr, var_type: String) -> Expr {
        Expr::Assignment(id, Box::new(expr), Some(var_type))
    }

    pub(crate) fn if_expr(cond: Expr, then: Expr, else_block: Option<Expr>) -> Expr {
        Expr::If(Box::new(cond), Box::new(then), else_block.map(Box::new))
    }

    pub(crate) fn while_expr(cond: Expr, block: Expr) -> Expr {
        Expr::While(Box::new(cond), Box::new(block))
    }

    pub(crate) fn no_op() -> Expr {
        Expr::NoOp
    }
}

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
                "Pushing top block: {:?}, top_block: {:?}",
                top_block.last().unwrap(),
                top_block
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

    fn parse_block(&mut self) -> Result<Option<Expr>, String> {
        let mut block = Vec::new();
        let start = self.pos;
        if let Some(Token::OpenCurly) = self.consume() {
            trace!(
                "Parsing block, tokens: {:?}",
                self.tokens.iter().skip(self.pos).collect::<Vec<_>>()
            );

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
                                self.tokens.iter().skip(self.pos).collect::<Vec<_>>()
                            );
                            block.push(expr);
                        }
                    }
                }
            }
            trace!("Parsed block: {:?}", block);
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
            if let Some(Token::Else) = self.consume() {
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
        self.parse_assignment()
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_assignment(&mut self) -> Result<Option<Expr>, String> {
        let start = self.pos;
        let left = match self.parse_comp() {
            Ok(Some(expr)) => expr,
            left @ _ => return left,
        };
        trace!("Parsed: {:?}", left);

        let var_type = match self.peek() {
            Some(Token::Colon) => {
                self.consume();
                let right = match self.parse_comp() {
                    Ok(Some(Expr::Identifier(id))) => id,
                    expr @ _ => return Err(format!("Expected type after ':', got {:?}", expr)),
                };
                Some(right)
            }
            _ => None,
        };

        if let Some(Token::Assign) = self.consume() {
            if let Expr::Identifier(id) = left {
                let right = match self.parse_comp() {
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
        if let Ok(Some(expr)) = self.parse_function() {
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
            Token::Ident(id) => Expr::Identifier(id),
            token => return Err(format!("Unexpected token: {:?}", token)),
        };
        Ok(Some(expr))
    }

    fn parse_function(&mut self) -> Result<Option<Expr>, String> {
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
                    return Ok(Some(Expr::Function(Token::Ident(fn_name), args)));
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
                self.consume(); // consume '('

                if let Some(Token::RightPar) = self.peek() {
                    self.consume(); // consume ')'
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
            assignment_typed("a".to_string(), num_lit(42), "int".to_string())
        );
    }
}
