use tracing::trace;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Token {
    NumLiteral(i32),
    StringLiteral(String),
    BoolLiteral(bool),
    Plus,
    Minus,
    LeftPar,
    RightPar,
    Mult,
    Div,
    Assign,
    Comma,
    SemiColon,
    GreaterThan,
    GreaterOrEqualThan,
    LessThan,
    LessOrEqualThan,
    Equal,
    OpenCurly,
    CloseCurly,
    If,
    Else,
    While,
    Ident(String),
}

pub(crate) fn tokenize(inp: &str) -> Result<Vec<Token>, String> {
    let inp = inp.chars().collect::<Vec<_>>();
    let mut tokens = Vec::new();
    let mut stack = Vec::new();

    let mut i = 0;
    while i < inp.len() {
        let c = inp[i];
        let token = match c {
            '0'..'9' => Some(tokenize_num(&mut i, &mut stack, &inp)?),
            '"' => Some(tokenize_string(&mut i, &mut stack, &inp)?),
            '(' => Some(Token::LeftPar),
            ')' => Some(Token::RightPar),
            '+' => Some(Token::Plus),
            '-' => Some(Token::Minus),
            '*' => Some(Token::Mult),
            '/' => Some(Token::Div),
            ' ' => None,
            ',' => Some(Token::Comma),
            ';' => Some(Token::SemiColon),
            '{' => Some(Token::OpenCurly),
            '}' => Some(Token::CloseCurly),
            '=' | '<' | '>' => Some(tokenize_comp(&mut i, &mut stack, &inp)?),
            '\n' | '\r' => None,
            'a'..='z' | 'A'..='Z' => Some(tokenize_multi_char(&mut i, &mut stack, &inp)),
            c => return Err(format!("Unimplemented char: {}", c)),
        };
        if let Some(token) = token {
            trace!("Pushing token: {:?}", token);
            tokens.push(token);
        }
        i += 1;
    }
    trace!("Tokens: {:?}", tokens);
    Ok(tokens)
}

fn tokenize_comp(i: &mut usize, _: &mut Vec<char>, inp: &[char]) -> Result<Token, String> {
    let curr = inp[*i];
    let next = inp.get(*i + 1);
    let t = match (curr, next) {
        ('=', Some('=')) => {
            *i += 1;
            Token::Equal
        }
        ('>', Some('=')) => {
            *i += 1;
            Token::GreaterOrEqualThan
        }
        ('<', Some('=')) => {
            *i += 1;
            Token::LessOrEqualThan
        }
        ('>', _) => Token::GreaterThan,
        ('<', _) => Token::LessThan,
        ('=', _) => Token::Assign,
        _ => Err(format!(
            "Invalid comparison operator, ({:?},{:?})",
            curr, next
        ))?,
    };
    Ok(t)
}

fn tokenize_num(i: &mut usize, stack: &mut Vec<char>, inp: &[char]) -> Result<Token, String> {
    while *i < inp.len() && matches!(inp[*i], '0'..='9') {
        stack.push(inp[*i]);
        *i += 1;
    }
    let num = stack
        .iter()
        .collect::<String>()
        .parse()
        .map_err(|e| format!("Invalid number ({:?}): {}", stack, e))?;
    trace!("Tokenized num: {}", num);
    stack.clear();
    *i -= 1;
    Ok(Token::NumLiteral(num))
}

fn tokenize_string(i: &mut usize, stack: &mut Vec<char>, inp: &[char]) -> Result<Token, String> {
    *i += 1;
    while *i < inp.len() && inp[*i] != '"' {
        stack.push(inp[*i]);
        *i += 1;
    }
    if *i == inp.len() {
        return Err("Unterminated string literal".to_string());
    }
    let string = stack.iter().collect::<String>();
    stack.clear();
    Ok(Token::StringLiteral(string))
}

fn tokenize_multi_char(i: &mut usize, stack: &mut Vec<char>, inp: &[char]) -> Token {
    while *i < inp.len() && matches!(inp[*i], 'a'..='z' | 'A'..='Z') {
        stack.push(inp[*i]);
        *i += 1;
    }
    let ident = stack.iter().collect::<String>();
    stack.clear();
    *i -= 1;
    built_in(&ident).unwrap_or(Token::Ident(ident))
}

fn built_in(s: &String) -> Option<Token> {
    match s.to_lowercase().as_str() {
        "true" => Some(Token::BoolLiteral(true)),
        "false" => Some(Token::BoolLiteral(false)),
        "ongod" => Some(Token::Assign),
        "glowup" => Some(Token::Plus),
        "glowdown" => Some(Token::Minus),
        ">=" => Some(Token::GreaterOrEqualThan),
        "<=" => Some(Token::LessOrEqualThan),
        "==" => Some(Token::Equal),
        "if" => Some(Token::If),
        "else" => Some(Token::Else),
        "while" => Some(Token::While),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenize() -> Result<(), String> {
        let inp = "yap(2 + 6 / 3)";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::Ident("yap".to_string()),
                Token::LeftPar,
                Token::NumLiteral(2),
                Token::Plus,
                Token::NumLiteral(6),
                Token::Div,
                Token::NumLiteral(3),
                Token::RightPar
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_semicolons() -> Result<(), String> {
        let inp = "2;5 / 3 + 4;4";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::NumLiteral(2),
                Token::SemiColon,
                Token::NumLiteral(5),
                Token::Div,
                Token::NumLiteral(3),
                Token::Plus,
                Token::NumLiteral(4),
                Token::SemiColon,
                Token::NumLiteral(4)
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_newline() -> Result<(), String> {
        let inp = "2\n5 / 3 + 4\n4";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::NumLiteral(2),
                Token::NumLiteral(5),
                Token::Div,
                Token::NumLiteral(3),
                Token::Plus,
                Token::NumLiteral(4),
                Token::NumLiteral(4)
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_variables() -> Result<(), String> {
        let inp: &str = "a=42;b=69";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::Ident("a".to_string()),
                Token::Assign,
                Token::NumLiteral(42),
                Token::SemiColon,
                Token::Ident("b".to_string()),
                Token::Assign,
                Token::NumLiteral(69),
            ]
        );
        Ok(())
    }

    #[test]
    fn tokeniz_gt_lt_eq() {
        let inp = "a > b; a < b; a >= b; a <= b; a == b; a=b";
        let tokens = tokenize(inp).unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::Ident("a".to_string()),
                Token::GreaterThan,
                Token::Ident("b".to_string()),
                Token::SemiColon,
                Token::Ident("a".to_string()),
                Token::LessThan,
                Token::Ident("b".to_string()),
                Token::SemiColon,
                Token::Ident("a".to_string()),
                Token::GreaterOrEqualThan,
                Token::Ident("b".to_string()),
                Token::SemiColon,
                Token::Ident("a".to_string()),
                Token::LessOrEqualThan,
                Token::Ident("b".to_string()),
                Token::SemiColon,
                Token::Ident("a".to_string()),
                Token::Equal,
                Token::Ident("b".to_string()),
                Token::SemiColon,
                Token::Ident("a".to_string()),
                Token::Assign,
                Token::Ident("b".to_string()),
            ]
        );
    }

    #[test]
    fn tokenize_if_with_else() {
        let inp = "if a > b { a = 42; } else { b = 69; }";
        let tokens = tokenize(inp).unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::If,
                Token::Ident("a".to_string()),
                Token::GreaterThan,
                Token::Ident("b".to_string()),
                Token::OpenCurly,
                Token::Ident("a".to_string()),
                Token::Assign,
                Token::NumLiteral(42),
                Token::SemiColon,
                Token::CloseCurly,
                Token::Else,
                Token::OpenCurly,
                Token::Ident("b".to_string()),
                Token::Assign,
                Token::NumLiteral(69),
                Token::SemiColon,
                Token::CloseCurly,
            ]
        );
    }

    #[test]
    fn if_else_if() -> Result<(), String> {
        let inp = "if a > b { 42; } else if a < b { 69; } else { 420; }";
        let tokens = tokenize(inp).unwrap();
        assert_eq!(
            tokens,
            vec![
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
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_windows_newline() -> Result<(), String> {
        let inp = "2\r\n5 / 3 + 4\r\n4";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::NumLiteral(2),
                Token::NumLiteral(5),
                Token::Div,
                Token::NumLiteral(3),
                Token::Plus,
                Token::NumLiteral(4),
                Token::NumLiteral(4)
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_while() -> Result<(), String> {
        let inp = "while a > b { a = a - 1; }";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::While,
                Token::Ident("a".to_string()),
                Token::GreaterThan,
                Token::Ident("b".to_string()),
                Token::OpenCurly,
                Token::Ident("a".to_string()),
                Token::Assign,
                Token::Ident("a".to_string()),
                Token::Minus,
                Token::NumLiteral(1),
                Token::SemiColon,
                Token::CloseCurly,
            ]
        );
        Ok(())
    }
}
