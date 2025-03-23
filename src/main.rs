use executer::execute;
use expression::Parser;
use tokenizer::tokenize;

mod executer;
mod expression;
mod tokenizer;

fn main() {
    let inp = "yap(2 + 6 / 3)";
    println!("Input: {}", inp);

    let tokens = tokenize(inp);
    println!("Tokens: {:?}", tokens);

    let mut parser = Parser::new(tokens);
    let expr = parser.parse().unwrap();
    println!("Expressions: {:?}", expr);

    let res = execute(expr);
    println!("Result: {:?}", res);
}
