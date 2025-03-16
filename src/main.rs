use std::io::Write;

use isa::compiler::{checker::Checker, infer::Substitute, parser::Parser};

fn main() {
    print!(">> ");
    std::io::stdout().flush().unwrap();
    for line in std::io::stdin().lines().map(Result::unwrap) {
        let mut parser = Parser::from_input(&line);

        let expr = match parser.parse() {
            Some(Ok(expr)) => expr,
            Some(Err(err)) => {
                eprintln!("{}: {}", err.span.start_loc(&line), err.data);
                return;
            }
            None => return,
        };

        let mut checker = Checker::new();
        let (mut expr, c) = match checker.check(expr) {
            Ok(ok) => ok,
            Err(err) => {
                eprintln!("{}", err);
                return;
            }
        };

        let subs = match checker.unify(c) {
            Ok(subs) => subs,
            Err(err) => {
                eprintln!("{}", err);
                return;
            }
        };

        for s in subs.iter() {
            print!("{}, ", s);
            expr.substitute(&s, checker.type_env_mut());
        }
        if !subs.is_empty() {
            println!()
        }

        println!("{}", expr);

        print!(">> ");
        std::io::stdout().flush().unwrap();
    }
}
