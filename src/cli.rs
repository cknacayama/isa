use std::path::PathBuf;

use crate::{
    compiler::{checker::Checker, infer::Substitute, parser::Parser},
    report::Report,
};

/// TODO: add more options
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Opt {
    #[default]
    Infer,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Config {
    opt:        Opt,
    input_path: PathBuf,
    bin_path:   PathBuf,
}

impl Config {
    #[must_use] pub fn from_env(mut env: std::env::Args) -> Self {
        let bin_path = PathBuf::from(
            env.next()
                .expect("Should have binary path as first argument"),
        );

        let input_path = PathBuf::from(
            env.next()
                .expect("Should have input path as second argument"),
        );

        let opt = env
            .next()
            .and_then(|opt| match opt.as_str() {
                "-i" => Some(Opt::Infer),
                _ => None,
            })
            .unwrap_or_default();

        Self {
            opt,
            input_path,
            bin_path,
        }
    }

    pub fn run(self) {
        let input =
            std::fs::read_to_string(self.input_path).expect("Should have valid path as input");
        let mut parser = Parser::from_input(&input);

        let modules = match parser.parse_all() {
            Ok(expr) if !expr.is_empty() => expr,
            Err(err) => return err.panic(&input),
            _ => return,
        };

        let mut checker = Checker::with_types(parser.types());

        let (mut modules, c) = match checker.check_many_modules(modules) {
            Ok(ok) => ok,
            Err(err) => return err.panic(&input),
        };

        let subs = match checker.unify(c) {
            Ok(subs) => subs,
            Err(err) => return err.panic(&input),
        };

        for module in &mut modules {
            module.substitute_many(&subs, checker.type_env_mut());
        }

        for module in modules {
            match module.name {
                Some(name) => println!("module {name}"),
                None => println!("module"),
            }
            for (id, ty) in &module.declared {
                println!("    val {id}: {ty};");
            }
        }
    }
}
