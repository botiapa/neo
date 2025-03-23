use crate::{
    expression::{BinaryOp, Expr},
    tokenizer::Token,
};

pub(crate) fn execute(expr: Expr) -> Expr {
    match expr {
        Expr::Binary(op, a, b) => match op {
            BinaryOp::Add => binary_op(add, *a, *b),
            BinaryOp::Sub => binary_op(sub, *a, *b),
            BinaryOp::Mult => binary_op(mult, *a, *b),
            BinaryOp::Div => binary_op(div, *a, *b),
        },
        Expr::Function(Token::Ident(ind), args) if ind == "yap" => {
            yap(args.get(0).expect("Expected argument"))
        }
        _ => unimplemented!(),
    }
}

fn expect_numlit(expr: Expr) -> Expr {
    match expr {
        Expr::NumLit(_) => expr,
        _ => execute(expr),
    }
}

fn expect_literal(expr: Expr) -> Expr {
    match expr {
        Expr::NumLit(_) | Expr::StringLit(_) => expr,
        _ => execute(expr),
    }
}

fn yap(a: &Expr) -> Expr {
    let arg = expect_literal(a.clone());
    let s = match arg {
        Expr::NumLit(a) => a.to_string(),
        Expr::StringLit(s) => s,
        _ => panic!("Invalid argument, expected number or string, got {:?}", arg),
    };
    println!("Yap: {}", s);
    Expr::NoOp
}

fn binary_op(op: fn(Expr, Expr) -> Expr, a: Expr, b: Expr) -> Expr {
    let a = expect_numlit(a);
    let b = expect_numlit(b);
    op(a, b)
}

fn add(a: Expr, b: Expr) -> Expr {
    if let (Expr::NumLit(a), Expr::NumLit(b)) = (&a, &b) {
        return Expr::NumLit(a + b);
    }
    panic!("Invalid addition, expected numbers, got {:?}", (a, b));
}

fn sub(a: Expr, b: Expr) -> Expr {
    if let (Expr::NumLit(a), Expr::NumLit(b)) = (&a, &b) {
        return Expr::NumLit(a - b);
    }
    panic!("Invalid subtraction, expected numbers, got {:?}", (a, b));
}

fn mult(a: Expr, b: Expr) -> Expr {
    if let (Expr::NumLit(a), Expr::NumLit(b)) = (&a, &b) {
        return Expr::NumLit(a * b);
    }
    panic!("Invalid multiplication, expected numbers, got {:?}", (a, b));
}

fn div(a: Expr, b: Expr) -> Expr {
    if let (Expr::NumLit(a), Expr::NumLit(b)) = (&a, &b) {
        return Expr::NumLit(a / b);
    }
    panic!("Invalid division, expected numbers, got {:?}", (a, b));
}
