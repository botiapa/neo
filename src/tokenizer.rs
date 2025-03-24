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
            '=' => Some(Token::Assign),
            ',' => Some(Token::Comma),
            ';' => Some(Token::SemiColon),
            '\n' => None,
            'a'..='z' | 'A'..='Z' => Some(tokenize_multi_char(&mut i, &mut stack, &inp)),
            c => return Err(format!("Unimplemented char: {}", c)),
        };
        if let Some(token) = token {
            trace!("Pushing token: {:?}", token);
            tokens.push(token);
        }
        i += 1;
    }
    Ok(tokens)
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
}
