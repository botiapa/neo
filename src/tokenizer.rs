#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Token {
    NumLiteral(i32),
    StringLiteral(String),
    Plus,
    Minus,
    LeftPar,
    RightPar,
    Mult,
    Div,
    True,
    False,
    Equal,
    Comma,
    Ident(String),
}

pub(crate) fn tokenize(inp: &str) -> Vec<Token> {
    let inp = inp.chars().collect::<Vec<_>>();
    let mut tokens = Vec::new();
    let mut stack = Vec::new();

    let mut i = 0;
    while i < inp.len() {
        let c = inp[i];
        let token = match c {
            '0'..'9' => Some(tokenize_num(&mut i, &mut stack, &inp)),
            '"' => Some(tokenize_string(&mut i, &mut stack, &inp)),
            '(' => Some(Token::LeftPar),
            ')' => Some(Token::RightPar),
            '+' => Some(Token::Plus),
            '-' => Some(Token::Minus),
            '*' => Some(Token::Mult),
            '/' => Some(Token::Div),
            ' ' => None,
            '=' => Some(Token::Equal),
            ',' => Some(Token::Comma),
            'a'..='z' | 'A'..='Z' => Some(tokenize_ident(&mut i, &mut stack, &inp)),
            _ => unimplemented!(),
        };
        if let Some(token) = token {
            tokens.push(token);
        }
        i += 1;
    }
    tokens
}

fn tokenize_num(i: &mut usize, stack: &mut Vec<char>, inp: &[char]) -> Token {
    while *i < inp.len() && matches!(inp[*i], '0'..'9') {
        stack.push(inp[*i]);
        *i += 1;
    }
    let num = stack
        .iter()
        .collect::<String>()
        .parse()
        .expect("Invalid number");
    stack.clear();
    *i -= 1;
    Token::NumLiteral(num)
}

fn tokenize_string(i: &mut usize, stack: &mut Vec<char>, inp: &[char]) -> Token {
    *i += 1;
    while *i < inp.len() && inp[*i] != '"' {
        stack.push(inp[*i]);
        *i += 1;
    }
    if *i == inp.len() {
        panic!("Unterminated string literal");
    }
    let string = stack.iter().collect::<String>();
    stack.clear();
    Token::StringLiteral(string)
}

fn tokenize_ident(i: &mut usize, stack: &mut Vec<char>, inp: &[char]) -> Token {
    while *i < inp.len() && matches!(inp[*i], 'a'..='z' | 'A'..='Z') {
        stack.push(inp[*i]);
        *i += 1;
    }
    let ident = stack.iter().collect::<String>();
    stack.clear();
    *i -= 1;
    match ident.as_str() {
        "true" => Token::True,
        "false" => Token::False,
        s => Token::Ident(s.to_string()),
    }
}
