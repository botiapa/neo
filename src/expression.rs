use tracing::{instrument, trace};

use crate::tokenizer::Token;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum UnaryOp {
    Plus,
    Minus,
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
    Assignment(String, Box<Expr>),
    NoOp,
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
        self.parse_expr()
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

    #[instrument(level = "trace", skip_all)]
    fn parse_expr(&mut self) -> Result<Option<Expr>, String> {
        trace!(
            "Parsing expr, tokens: {:?}",
            self.tokens.iter().skip(self.pos).collect::<Vec<_>>()
        );

        let expr = match self.parse_assignment() {
            Ok(Some(expr)) => expr,
            expr @ _ => return expr,
        };

        trace!("Parsed expr: {:?}", expr);
        let mut block = vec![expr.clone()];
        while let Some(Token::SemiColon) = self.peek() {
            self.consume();
            if let Ok(Some(expr)) = self.parse_assignment() {
                trace!("Adding expr to block: {:?}", expr);
                block.push(expr);
            } else {
                break;
            }
        }
        if block.len() > 1 {
            Ok(Some(Expr::Block(block)))
        } else {
            Ok(Some(expr))
        }
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_assignment(&mut self) -> Result<Option<Expr>, String> {
        let start = self.pos;
        if let Some(Token::Ident(var_name)) = self.consume() {
            if let Some(Token::Assign) = self.consume() {
                let expr = match self.parse_assignment() {
                    Ok(Some(expr)) => expr,
                    expr @ _ => return expr,
                };
                trace!("Parsed assignment: {} = {:?}", var_name, expr);
                return Ok(Some(Expr::Assignment(var_name, Box::new(expr))));
            }
        }
        self.pos = start;
        self.parse_comp()
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_comp(&mut self) -> Result<Option<Expr>, String> {
        let mut left = match self.parse_add_sub() {
            Ok(Some(expr)) => expr,
            left @ _ => return left,
        };
        trace!("Parsed: {:?}", left);

        if let Some(token) = self.peek() {
            match token {
                Token::GreaterThan
                | Token::GreaterOrEqualThan
                | Token::LessThan
                | Token::LessOrEqualThan
                | Token::Equal => {
                    self.consume();
                    let right = match self.parse_add_sub() {
                        Ok(Some(expr)) => expr,
                        expr @ _ => return expr,
                    };

                    left = match token {
                        Token::GreaterThan => {
                            Expr::Binary(BinaryOp::GreaterThan, Box::new(left), Box::new(right))
                        }
                        Token::GreaterOrEqualThan => Expr::Binary(
                            BinaryOp::GreaterOrEqualThan,
                            Box::new(left),
                            Box::new(right),
                        ),
                        Token::LessThan => {
                            Expr::Binary(BinaryOp::LessThan, Box::new(left), Box::new(right))
                        }
                        Token::LessOrEqualThan => {
                            Expr::Binary(BinaryOp::LessOrEqualThan, Box::new(left), Box::new(right))
                        }
                        Token::Equal => {
                            Expr::Binary(BinaryOp::Equal, Box::new(left), Box::new(right))
                        }
                        _ => unreachable!(),
                    };
                }
                _ => {}
            }
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

                    left = match token {
                        Token::GreaterThan => {
                            Expr::Binary(BinaryOp::GreaterThan, Box::new(left), Box::new(right))
                        }
                        Token::GreaterOrEqualThan => Expr::Binary(
                            BinaryOp::GreaterOrEqualThan,
                            Box::new(left),
                            Box::new(right),
                        ),
                        Token::LessThan => {
                            Expr::Binary(BinaryOp::LessThan, Box::new(left), Box::new(right))
                        }
                        Token::LessOrEqualThan => {
                            Expr::Binary(BinaryOp::LessOrEqualThan, Box::new(left), Box::new(right))
                        }
                        Token::Equal => {
                            Expr::Binary(BinaryOp::Equal, Box::new(left), Box::new(right))
                        }
                        Token::Plus => Expr::Binary(BinaryOp::Add, Box::new(left), Box::new(right)),
                        Token::Minus => {
                            Expr::Binary(BinaryOp::Sub, Box::new(left), Box::new(right))
                        }
                        _ => unreachable!(),
                    };
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

                    left = match token {
                        Token::Mult => {
                            Expr::Binary(BinaryOp::Mult, Box::new(left), Box::new(right))
                        }
                        Token::Div => Expr::Binary(BinaryOp::Div, Box::new(left), Box::new(right)),
                        _ => unreachable!(),
                    };
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

        match expr {
            Token::NumLiteral(n) => Ok(Some(Expr::NumLit(n))),
            Token::StringLiteral(s) => Ok(Some(Expr::StringLit(s))),
            Token::BoolLiteral(b) => Ok(Some(Expr::BoolLit(b))),
            Token::Ident(id) => Ok(Some(Expr::Identifier(id))),
            token => Err(format!("Unexpected token: {:?}", token)),
        }
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

    use crate::expression::BinaryOp;

    use super::{Expr, Parser, Token};

    #[test]
    fn parse_single_expr() {
        let mut parser = Parser::new(vec![Token::NumLiteral(42)]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(expr, Expr::NumLit(42));
    }

    #[test]
    fn parse_block() {
        let mut parser = Parser::new(vec![
            Token::NumLiteral(1),
            Token::SemiColon,
            Token::NumLiteral(2),
            Token::SemiColon,
            Token::NumLiteral(3),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            Expr::Block(vec![Expr::NumLit(1), Expr::NumLit(2), Expr::NumLit(3)])
        );
    }

    #[test]
    fn parse_assignment() {
        let mut parser = Parser::new(vec![
            Token::Ident("a".to_string()),
            Token::Assign,
            Token::NumLiteral(42),
        ]);
        let expr = parser.parse().unwrap().unwrap();
        assert_eq!(
            expr,
            Expr::Assignment("a".to_string(), Box::new(Expr::NumLit(42)))
        );
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
            Expr::Block(vec![
                Expr::Assignment("a".to_string(), Box::new(Expr::NumLit(42))),
                Expr::Identifier("a".to_string())
            ])
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
        assert_eq!(
            expr,
            Expr::Binary(
                super::BinaryOp::Equal,
                Box::new(Expr::NumLit(1)),
                Box::new(Expr::NumLit(2))
            )
        );
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
            Expr::Binary(
                BinaryOp::Equal,
                Box::new(Expr::Binary(
                    super::BinaryOp::Add,
                    Box::new(Expr::NumLit(1)),
                    Box::new(Expr::NumLit(1))
                )),
                Box::new(Expr::Binary(
                    super::BinaryOp::Add,
                    Box::new(Expr::NumLit(1)),
                    Box::new(Expr::NumLit(1))
                )),
            )
        );
    }
}
