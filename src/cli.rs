use std::ffi::OsStr;
use std::fmt::Debug;
use std::path::PathBuf;
use std::time::Instant;

use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

use crate::compiler::checker::Checker;
use crate::compiler::ctx::TypeCtx;
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
        }
    }

    fn report<E>(&self, err: &E, ctx: &TypeCtx)
    where
        E: Report,
    {
        let writer = StandardStream::stderr(ColorChoice::Auto);
        let config = term::Config {
            chars: term::Chars::ascii(),
            ..Default::default()
        };
        let diagnostic = err.diagnostic(self.file_id, ctx);

        let _ = term::emit(&mut writer.lock(), &config, &self.files, &diagnostic);
    }

    pub fn run(&self) {
        let input = self
            .files
            .get(self.file_id)
            .unwrap_or_else(|_| unreachable!())
            .source();

        let start = Instant::now();

        let mut parser = Parser::from_input(input);

        let modules = match parser.parse_all() {
            Ok(expr) if !expr.is_empty() => expr,
            Err(err) => return self.report(&err, &TypeCtx::default()),
            _ => return,
        };

        let mut checker = Checker::new();

        let modules = match checker.check_many_modules(modules) {
            Ok(ok) => ok,
            Err(err) => return self.report(&err, checker.type_ctx()),
        };

        for module in modules {
            if let Err(err) = check_matches(&module.exprs, checker.type_ctx()) {
                return self.report(&err, checker.type_ctx());
            }
        }

        let duration = start.elapsed();

        for (module, declared) in checker.modules() {
            println!("module {module}");
            for (id, ty) in declared {
                println!("    val {id}: {};", ty.ty());
            }
        }

        println!("ran in {duration:?}");
    }
}
