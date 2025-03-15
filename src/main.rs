use isa::compiler::{checker::Checker, infer::Substitute, parser::Parser};

fn main() {
    let file_name = "in/input.isa";

    let input = std::fs::read_to_string(file_name).expect("should be a valid file");

    let mut parser = Parser::from_input(&input);

    let expr = match parser.parse() {
        Some(Ok(expr)) => expr,
        Some(Err(err)) => {
            eprintln!("{}: {}", err.span.start_loc(&input), err.data);
            return;
        }
        None => return,
    };

    let mut checker = Checker::new();
    let (expr, mut c) = match checker.check(expr) {
        Ok(ok) => ok,
        Err(err) => {
            eprintln!("{}", err);
            return;
        }
    };

    println!("{}", expr);
    println!("{}", c);

    let subs = match checker.unify(c.clone()) {
        Ok(subs) => subs,
        Err(err) => {
            eprintln!("{}", err);
            return;
        }
    };

    for s in subs {
        print!("{{{}}}, ", s);
        c = c.substitute(&s, checker.type_env_mut());
    }
    println!();

    println!("{}", c);
}
