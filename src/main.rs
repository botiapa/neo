use std::{
    env,
    fs::File,
    io::{Read, stdin},
    path::Path,
};

use executer::{Context, execute};
use expression::Parser;
use tokenizer::tokenize;
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

    let args: Vec<String> = env::args().collect();
    if args.len() == 1 {
        interactive_mode();
    } else if args.len() == 2 {
        check_arg(&args[1]);
    } else {
        panic!("Invalid number of arguments");
    }
}

fn interactive_mode() {
    let mut context = Context::new();
    for line in stdin().lines() {
        if let Ok(line) = line {
            let tokens = tokenize(&line);
            let mut parser = Parser::new(tokens);
            let expr = parser.parse().unwrap();
            let res = execute(&mut context, expr);
            context.flush_stdout().expect("Failed writing to stdout");
            println!("Result: {:?}", res);
        }
    }
}

fn check_arg(arg: &str) {
    let p = Path::new(arg);
    if let Ok(exists) = p.try_exists() {
        if exists {
            let mut s = String::new();
            let mut f = File::open(p).expect("failed opening file");
            f.read_to_string(&mut s).expect("failed reading file");
            interpret_string(&s);
            return;
        }
    }
    interpret_string(arg);
}

fn interpret_string(inp: &str) {
    let mut context = Context::new();
    let tokens = tokenize(&inp);
    let mut parser = Parser::new(tokens);
    let expr = parser.parse().unwrap();
    let res = execute(&mut context, expr);
    context.flush_stdout().expect("Failed writing to stdout");
    println!("Result: {:?}", res);
}
