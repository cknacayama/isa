use isa::compiler::{checker::Checker, infer::Substitute, parser::Parser};

fn main() {
    let input = std::fs::read_to_string("in/input.isa").unwrap();

    let mut parser = Parser::from_input(&input);

    let expr = match parser.parse_all() {
        Ok(expr) if !expr.is_empty() => expr,
        Err(err) => {
            eprintln!("{}: {}", err.span.start_loc(&input), err.data);
            return;
        }
        _ => return,
    };

    let mut checker = Checker::new();

    let (mut expr, c) = match checker.check_many(expr) {
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
    }
    for e in expr.iter_mut() {
        e.substitute_many(&subs, checker.type_env_mut());
    }
    if !subs.is_empty() {
        println!()
    }

    for expr in expr {
        println!("{}", expr);
    }

    for (id, ty) in checker.env().iter() {
        println!("{}: {}", id, ty);
    }
}
