use isa::compiler::{checker::Checker, infer::Substitute, parser::Parser};

fn main() {
    let input = std::fs::read_to_string("in/list.isa").unwrap();

    let mut parser = Parser::from_input(&input);

    let expr = match parser.parse_all() {
        Ok(expr) if !expr.is_empty() => expr,
        Err(err) => {
            eprintln!("{}: {}", err.span.start_loc(&input), err.data);
            return;
        }
        _ => return,
    };

    let mut checker = Checker::with_types(parser.types());

    let (mut expr, c) = match checker.check_many(expr) {
        Ok(ok) => ok,
        Err(err) => {
            eprintln!("{err}");
            return;
        }
    };

    let subs = match checker.unify(c) {
        Ok(subs) => subs,
        Err(err) => {
            eprintln!("{err}");
            return;
        }
    };

    for e in &mut expr {
        e.substitute_many(&subs, checker.type_env_mut());
    }

    for expr in expr {
        println!("{}", expr.format());
    }
    for (id, ty) in checker.env().iter() {
        println!("val {id}: {ty};");
    }
}
