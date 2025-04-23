use tracing::trace;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Token {
    /// `123`
    NumLiteral(i32),
    /// `"Hello, world!"`
    StringLiteral(String),
    /// `true`
    BoolLiteral(bool),
    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `(`
    LeftPar,
    /// `)`
    RightPar,
    /// `*`
    Mult,
    /// `/`
    Div,
    /// `=`
    Assign,
    /// `,`
    Comma,
    /// `;`
    SemiColon,
    /// `>`
    GreaterThan,
    /// `>=`
    GreaterOrEqualThan,
    /// `<`
    LessThan,
    /// `<=`
    LessOrEqualThan,
    /// `==`
    Equal,
    /// `{`
    OpenCurly,
    /// `}`
    CloseCurly,
    /// `if`
    If,
    /// `else`
    Else,
    /// `while`
    While,
    /// `!`
    Negate,
    /// `:`
    Colon,
    /// `::`
    DoubleColon,
    /// `fn`
    Function,
    /// `enum`
    Enum,
    /// `is`
    Is,
    /// `Ident(String)`
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
            '0'..='9' => Some(tokenize_num(&mut i, &mut stack, &inp)?),
            '"' => Some(tokenize_string(&mut i, &mut stack, &inp)?),
            '(' => Some(Token::LeftPar),
            ')' => Some(Token::RightPar),
            '+' => Some(Token::Plus),
            '-' => Some(Token::Minus),
            '*' => Some(Token::Mult),
            '/' => {
                if let Some('/') = inp.get(i + 1) {
                    tokenize_comment(&mut i, &inp)?;
                    continue;
                }
                Some(Token::Div)
            }
            ' ' => None,
            ',' => Some(Token::Comma),
            ':' => Some(tokenize_colon(&mut i, &inp)?),
            ';' => Some(Token::SemiColon),
            '{' => Some(Token::OpenCurly),
            '}' => Some(Token::CloseCurly),
            '!' => Some(Token::Negate),
            '=' | '<' | '>' => Some(tokenize_comp(&mut i, &mut stack, &inp)?),
            '\n' | '\r' => None,
            'a'..='z' | 'A'..='Z' | '?' => Some(tokenize_multi_char(&mut i, &mut stack, &inp)),
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

fn tokenize_colon(i: &mut usize, inp: &[char]) -> Result<Token, String> {
    if let Some(':') = inp.get(*i + 1) {
        *i += 1;
        Ok(Token::DoubleColon)
    } else {
        Ok(Token::Colon)
    }
}

fn tokenize_comment(i: &mut usize, inp: &[char]) -> Result<(), String> {
    while *i < inp.len() && inp[*i] != '\n' {
        *i += 1;
    }
    Ok(())
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
    while *i < inp.len() && matches!(inp[*i], 'a'..='z' | 'A'..='Z' | '?') {
        stack.push(inp[*i]);
        *i += 1;
    }
    let ident = stack.iter().collect::<String>();
    stack.clear();
    *i -= 1;
    built_in(&ident).unwrap_or_else(|| built_in_cursed(&ident).unwrap_or(Token::Ident(ident)))
}

fn built_in(s: &String) -> Option<Token> {
    match s.to_lowercase().as_str() {
        "true" => Some(Token::BoolLiteral(true)),
        "false" => Some(Token::BoolLiteral(false)),
        ">=" => Some(Token::GreaterOrEqualThan),
        "<=" => Some(Token::LessOrEqualThan),
        "if" => Some(Token::If),
        "else" => Some(Token::Else),
        "while" => Some(Token::While),
        "fn" => Some(Token::Function),
        "enum" => Some(Token::Enum),
        "is" => Some(Token::Is),
        _ => None,
    }
}

fn built_in_cursed(s: &String) -> Option<Token> {
    match s.to_lowercase().as_str() {
        "bet" => Some(Token::Assign),
        "glowup" => Some(Token::Plus),
        "glowdown" => Some(Token::Minus),
        "cap" => Some(Token::Negate),
        "fr?" => Some(Token::If),
        "nah" => Some(Token::Else),
        "cook" => Some(Token::While),
        "pack" => Some(Token::Function),
        "be" => Some(Token::Is),
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

    #[test]
    fn tokenize_comment() -> Result<(), String> {
        let inp = "//This is a comment \n 42";
        let tokens = tokenize(inp)?;
        assert_eq!(tokens, vec![Token::NumLiteral(42)]);
        Ok(())
    }

    #[test]
    fn tokenize_negate() -> Result<(), String> {
        let inp = "!true";
        let tokens = tokenize(inp)?;
        assert_eq!(tokens, vec![Token::Negate, Token::BoolLiteral(true)]);
        Ok(())
    }

    #[test]
    fn tokenize_negate_cursed() -> Result<(), String> {
        let inp = "cap true";
        let tokens = tokenize(inp)?;
        assert_eq!(tokens, vec![Token::Negate, Token::BoolLiteral(true)]);
        Ok(())
    }

    #[test]
    fn tokenize_cursed_if() -> Result<(), String> {
        let inp = "fr? a > b { 42; } else { 69; }";
        let tokens = tokenize(inp)?;
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
                Token::OpenCurly,
                Token::NumLiteral(69),
                Token::SemiColon,
                Token::CloseCurly,
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_assign() -> Result<(), String> {
        let inp = "a bet 42";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::Ident("a".to_string()),
                Token::Assign,
                Token::NumLiteral(42)
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_cursed_else() -> Result<(), String> {
        let inp = "a nah 42";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::Ident("a".to_string()),
                Token::Else,
                Token::NumLiteral(42)
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_cursed_while() -> Result<(), String> {
        let inp = "a cook 42 { a = a + 1; }";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::Ident("a".to_string()),
                Token::While,
                Token::NumLiteral(42),
                Token::OpenCurly,
                Token::Ident("a".to_string()),
                Token::Assign,
                Token::Ident("a".to_string()),
                Token::Plus,
                Token::NumLiteral(1),
                Token::SemiColon,
                Token::CloseCurly,
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_colon() -> Result<(), String> {
        let inp = "a:int";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::Ident("a".to_string()),
                Token::Colon,
                Token::Ident("int".to_string())
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_function() -> Result<(), String> {
        let inp = "fn a(b:int) { b = b + 1; }";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::Function,
                Token::Ident("a".to_string()),
                Token::LeftPar,
                Token::Ident("b".to_string()),
                Token::Colon,
                Token::Ident("int".to_string()),
                Token::RightPar,
                Token::OpenCurly,
                Token::Ident("b".to_string()),
                Token::Assign,
                Token::Ident("b".to_string()),
                Token::Plus,
                Token::NumLiteral(1),
                Token::SemiColon,
                Token::CloseCurly,
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_enum() -> Result<(), String> {
        let inp = "enum A { B(int, int), C }";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
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
                Token::CloseCurly
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_double_colon() -> Result<(), String> {
        let inp = "A::B";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::Ident("A".to_string()),
                Token::DoubleColon,
                Token::Ident("B".to_string())
            ]
        );
        Ok(())
    }

    #[test]
    fn tokenize_is() -> Result<(), String> {
        let inp = "a is A(n)";
        let tokens = tokenize(inp)?;
        assert_eq!(
            tokens,
            vec![
                Token::Ident("a".to_string()),
                Token::Is,
                Token::Ident("A".to_string()),
                Token::LeftPar,
                Token::Ident("n".to_string()),
                Token::RightPar
            ]
        );
        Ok(())
    }
}
