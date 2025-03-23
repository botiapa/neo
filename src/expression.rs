use crate::tokenizer::Token;

#[derive(Debug, Clone)]
pub(crate) enum UnaryOp {
    Plus,
    Minus,
}

#[derive(Debug, Clone)]
pub(crate) enum BinaryOp {
    Add,
    Sub,
    Mult,
    Div,
}

#[derive(Debug, Clone)]
pub(crate) enum Expr {
    NumLit(i32),
    StringLit(String),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    Function(Token, Vec<Expr>),
    NoOp,
}

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

    fn parse_expr(&mut self) -> Option<Expr> {
        self.parse_add_sub()
    }

    fn parse_add_sub(&mut self) -> Option<Expr> {
        let mut left = self.parse_mult_div()?;

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
