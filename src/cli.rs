use std::ffi::OsStr;
use std::fmt::Debug;
use std::path::PathBuf;
use std::time::Instant;

use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

use crate::compiler::checker::Checker;
use crate::compiler::ctx::Ctx;
use crate::compiler::exhaust::check_matches;
use crate::compiler::parser::Parser;
use crate::report::Report;

/// TODO: add more options
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Opt {
    #[default]
    Infer,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Default)]
pub struct Config {
    opt:        Opt,
    input_path: PathBuf,
    bin_path:   PathBuf,
    files:      SimpleFiles<String, String>,
    file_id:    usize,
    prelude_id: usize,
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

        let mut files = SimpleFiles::new();
        let input_file_name = input_path
            .file_name()
            .and_then(OsStr::to_str)
            .unwrap_or_default()
            .to_owned();
        let file_id = files.add(input_file_name, input);
        let prelude_id = Self::add_prelude(&mut files);

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
            files,
            file_id,
            prelude_id,
        }
    }

    fn add_prelude(files: &mut SimpleFiles<String, String>) -> usize {
        let input_path = PathBuf::from("stdlib/prelude.isa");
        let input = std::fs::read_to_string(&input_path).expect("Should have valid path as input");
        let input_file_name = input_path
            .file_name()
            .and_then(OsStr::to_str)
            .unwrap_or_default()
            .to_owned();
        files.add(input_file_name, input)
    }

    fn report<E>(&self, err: &E, ctx: &Ctx, id: usize)
    where
        E: Report,
    {
        let writer = StandardStream::stderr(ColorChoice::Auto);
        let config = term::Config::default();
        let diagnostic = err.diagnostic(id, ctx);

        let _ = term::emit(&mut writer.lock(), &config, &self.files, &diagnostic);
    }

    fn compile(&self, mut checker: Checker, id: usize) -> Checker {
        let input = self.files.get(id).unwrap().source();
        let start = Instant::now();

        let mut parser = Parser::from_input(input);

        let modules = match parser.parse_all() {
            Ok(expr) if !expr.is_empty() => expr,
            Err(err) => {
                self.report(&err, &Ctx::default(), id);
                return checker;
            }
            _ => return checker,
        };

        let end_parse = Instant::now();

        let (modules, set) = match checker.check_many_modules(modules) {
            Ok(ok) => ok,
            Err(err) => {
                self.report(&err, &Ctx::default(), id);
                return checker;
            }
        };

        let end_check = Instant::now();

        for module in modules {
            if let Err(err) = check_matches(&module.exprs, checker.ctx()) {
                self.report(&err, &Ctx::default(), id);
                return checker;
            }
        }

        let end_exhaust = Instant::now();

        let duration = end_exhaust.duration_since(start);

        println!("{}", checker.ctx());
        println!("where");
        for c in set.iter() {
            println!("  {} {},", c.class(), c.ty());
        }

        println!("ran in {duration:?}");
        println!("  parsing in {:?}", end_parse.duration_since(start));
        println!(
            "  type analysis in {:?}",
            end_check.duration_since(end_parse)
        );
        println!(
            "  exhaustivness check in {:?}",
            end_exhaust.duration_since(end_check)
        );

        checker
    }

    pub fn run(&self) {
        let prelude = self.compile(Checker::default(), self.prelude_id);
        self.compile(prelude, self.file_id);
    }
}
