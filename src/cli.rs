use std::fmt::Debug;
use std::path::PathBuf;
use std::time::Instant;

use crate::compiler::checker::Checker;
use crate::compiler::exhaust::check_matches;
use crate::compiler::parser::Parser;

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
    input:      String,
}

impl Config {
    /// # Panics
    ///
    /// Will panic if any arguments are missing
    /// Or if input file does not exist
    #[must_use]
    pub fn from_env(mut env: std::env::Args) -> Self {
        let bin_path = PathBuf::from(
            env.next()
                .expect("Should have binary path as first argument"),
        );

        let input_path = PathBuf::from(
            env.next()
                .expect("Should have input path as second argument"),
        );

        let input = std::fs::read_to_string(&input_path).expect("Should have valid path as input");

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
            input,
        }
    }

    pub fn run(self) {
        let input = self.input;

        let start = Instant::now();

        let mut parser = Parser::from_input(&input);

        let modules = match parser.parse_all() {
            Ok(expr) if !expr.is_empty() => expr,
            Err(err) => return err.report(&input),
            _ => return,
        };

        let mut checker = Checker::new();

        let modules = match checker.check_many_modules(modules) {
            Ok(ok) => ok,
            Err(err) => return err.report(&input),
        };

        let duration = start.elapsed();

        for module in modules {
            if let Err(err) = check_matches(&module.exprs, checker.type_ctx()) {
                return err.report(checker.type_ctx(), &input);
            }

            match module.name {
                Some(name) => println!("module {name}"),
                None => println!("module"),
            }
            for (id, ty) in &module.declared {
                println!("    val {id}: {};", ty.ty());
            }
        }

        println!("ran in {duration:?}");
    }
}
