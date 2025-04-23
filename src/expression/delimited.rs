use crate::tokenizer::Token;

use super::Parser;

impl Parser {
    pub(super) fn parse_delimited<T>(
        &mut self,
        delim: Token,
        start: Token,
        end: Token,
        parse_item: impl Fn(&mut Parser) -> Result<T, String>,
    ) -> Result<Option<Vec<T>>, String> {
        if self.peek() != Some(start) {
            return Ok(None);
        }
        self.consume();

        let mut items = Vec::new();

        // The first item is either end or a parse_item
        if self.peek().as_ref() == Some(&end) {
            self.consume();
            return Ok(Some(items));
        } else {
            items.push(parse_item(self)?);
        }

        // The rest of the items are either end or delimited items
        loop {
            if self.peek().as_ref() == Some(&end) {
                self.consume();
                break;
            } else if self.peek().as_ref() == Some(&delim) {
                self.consume();
                // the next token has to be a parse_item
                items.push(parse_item(self)?);
            } else {
                return Err("Expected ',' or ')' after last field".to_string());
            }
        }
        Ok(Some(items))
    }

    pub(super) fn parse_delimited_idents(
        &mut self,
        delim: Token,
        start: Token,
        end: Token,
    ) -> Result<Option<Vec<String>>, String> {
        self.parse_delimited(delim, start, end, |parser| {
            if let Some(Token::Ident(ident)) = parser.peek() {
                parser.consume();
                Ok(ident)
            } else {
                Err("Expected identifier".to_string())
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::Parser;

    use super::*;

    #[test]
    fn parse_delimited_idents() {
        // (a, b)
        let mut parser = Parser::new(vec![
            Token::LeftPar,
            Token::Ident("a".to_string()),
            Token::Comma,
            Token::Ident("b".to_string()),
            Token::RightPar,
        ]);
        let result = parser
            .parse_delimited_idents(Token::Comma, Token::LeftPar, Token::RightPar)
            .unwrap();
        assert_eq!(result, Some(vec!["a".to_string(), "b".to_string()]));
        assert!(parser.empty());
    }

    #[test]
    fn parse_unclosed_delimited_idents() {
        // (a,b
        let mut parser = Parser::new(vec![
            Token::LeftPar,
            Token::Ident("a".to_string()),
            Token::Comma,
            Token::Ident("b".to_string()),
        ]);
        let result = parser.parse_delimited_idents(Token::Comma, Token::LeftPar, Token::RightPar);
        assert_eq!(
            result,
            Err("Expected ',' or ')' after last field".to_string())
        );

        // (a,
        let mut parser = Parser::new(vec![
            Token::LeftPar,
            Token::Ident("a".to_string()),
            Token::Comma,
        ]);
        let result = parser.parse_delimited_idents(Token::Comma, Token::LeftPar, Token::RightPar);
        assert_eq!(result, Err("Expected identifier".to_string()));

        // (a
        let mut parser = Parser::new(vec![Token::LeftPar, Token::Ident("a".to_string())]);
        let result = parser.parse_delimited_idents(Token::Comma, Token::LeftPar, Token::RightPar);
        assert_eq!(
            result,
            Err("Expected ',' or ')' after last field".to_string())
        );
        assert!(parser.empty());
    }
}
