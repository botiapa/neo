use executer::{Context, execute};
use expression::Parser;
use tokenizer::tokenize;
use tracing::{error, info, level_filters::LevelFilter, trace};
use tracing_subscriber::EnvFilter;

mod executer;
mod expression;
mod tokenizer;

fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .with_level(false)
        .without_time()
        .init();

    let inp = "a=42;yap(a)";
    println!("Input: {}", inp);

    let tokens = tokenize(inp);
    println!("Tokens: {:?}", tokens);

    let mut parser = Parser::new(tokens);
    let expr = parser.parse().unwrap();
    println!("Expressions: {:?}", expr);

    let mut context = Context::new();
    let res = execute(&mut context, expr.into());
    context.flush_stdout().expect("Failed writing to stdout");
    println!("\nResult: {:?}", res);
}
