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
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Expr {
    NumLit(i32),
    StringLit(String),
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

    pub(crate) fn parse(&mut self) -> Option<Expr> {
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
    fn parse_expr(&mut self) -> Option<Expr> {
        trace!(
            "Parsing expr, tokens: {:?}",
            self.tokens.iter().skip(self.pos + 1).collect::<Vec<_>>()
        );
        let expr = self.parse_assignment()?;
        trace!("Parsed expr: {:?}", expr);
        let mut block = vec![expr.clone()];
        while let Some(Token::SemiColon) = self.peek() {
            self.consume();
            if let Some(expr) = self.parse_assignment() {
                trace!("Adding expr to block: {:?}", expr);
                block.push(expr);
            } else {
                break;
            }
        }
        if block.len() > 1 {
            Some(Expr::Block(block))
        } else {
            Some(expr)
        }
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_assignment(&mut self) -> Option<Expr> {
        let start = self.pos;
        if let Some(Token::Ident(var_name)) = self.consume() {
            if let Some(Token::Assign) = self.consume() {
                let expr = self.parse_assignment()?;
                trace!("Parsed assignment: {} = {:?}", var_name, expr);
                return Some(Expr::Assignment(var_name, Box::new(expr)));
            }
        }
        self.pos = start;
        self.parse_add_sub()
    }

    #[instrument(level = "trace", skip_all)]
    fn parse_add_sub(&mut self) -> Option<Expr> {
        let mut left = self.parse_mult_div()?;
        trace!("Parsed: {:?}", left);

        while let Some(token) = self.peek() {
            match token {
                Token::Plus | Token::Minus => {
                    self.consume();
                    let right = self.parse_mult_div()?;
                    left = match token {
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
        Some(left)
    }

    fn parse_mult_div(&mut self) -> Option<Expr> {
        let mut left = self.parse_primary()?;

        while let Some(token) = self.peek() {
            match token {
                Token::Mult | Token::Div => {
                    self.consume();
                    let right = self.parse_primary()?;
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
        Some(left)
    }

    fn parse_primary(&mut self) -> Option<Expr> {
        if let Some(expr) = self.parse_function() {
            return Some(expr);
        }

        if let Some(expr) = self.parse_unary() {
            return Some(expr);
        }

        if let Some(expr) = self.parse_paren() {
            return Some(expr);
        }

        match self.consume()? {
            Token::NumLiteral(n) => Some(Expr::NumLit(n)),
            Token::StringLiteral(s) => Some(Expr::StringLit(s)),
            Token::Ident(id) => Some(Expr::Identifier(id)),
            token => panic!("Unexpected token: {:?}", token),
        }
    }

    fn parse_function(&mut self) -> Option<Expr> {
        let start = self.pos;

        if let Some(Token::Ident(fn_name)) = self.consume() {
            if let Some(Token::LeftPar) = self.consume() {
                let mut args = Vec::new();
                while self.peek() != Some(Token::RightPar) {
                    let arg = self.parse_expr()?;
                    args.push(arg);
                    if let Some(Token::Comma) = self.peek() {
                        self.consume();
                    }
                }
                if let Some(Token::RightPar) = self.consume() {
                    return Some(Expr::Function(Token::Ident(fn_name), args));
                }
                panic!("Expected ')' after function arguments");
            }
        }
        self.pos = start;
        None
    }

    fn parse_unary(&mut self) -> Option<Expr> {
        match self.peek()? {
            Token::Plus => {
                self.consume();
                let expr = self.parse_primary()?;
                Some(Expr::Unary(UnaryOp::Plus, Box::new(expr)))
            }
            Token::Minus => {
                self.consume();
                let expr = self.parse_primary()?;
                Some(Expr::Unary(UnaryOp::Minus, Box::new(expr)))
            }
            _ => None,
        }
    }

    fn parse_paren(&mut self) -> Option<Expr> {
        match self.peek()? {
            Token::LeftPar => {
                self.consume(); // consume '('

                if let Some(Token::RightPar) = self.peek() {
                    self.consume(); // consume ')'
                    return None;
                }

                let expr = self.parse_expr();
                if self.consume() != Some(Token::RightPar) {
                    panic!("Expected ')'");
                }
                expr
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {

    use super::{Expr, Parser, Token};

    #[test]
    fn parse_single_expr() {
        let mut parser = Parser::new(vec![Token::NumLiteral(42)]);
        let expr = parser.parse().unwrap();
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
        let expr = parser.parse().unwrap();
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
        let expr = parser.parse().unwrap();
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
        let expr = parser.parse().unwrap();
        assert_eq!(
            expr,
            Expr::Block(vec![
                Expr::Assignment("a".to_string(), Box::new(Expr::NumLit(42))),
                Expr::Identifier("a".to_string())
            ])
        );
    }
}
