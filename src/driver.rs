use std::ffi::OsStr;
use std::fmt::{Debug, Display, Write};
use std::path::PathBuf;
use std::time::{Duration, Instant};

use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::files::{Files, SimpleFile};
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use codespan_reporting::{files, term};
use rustc_hash::FxHashSet;

use crate::compiler::ast::Module;
use crate::compiler::checker::Checker;
use crate::compiler::ctx::Ctx;
use crate::compiler::exhaust::check_matches;
use crate::compiler::lexer::Lexer;
use crate::compiler::parser::Parser;
use crate::compiler::token::Token;
use crate::compiler::types::Ty;
use crate::report::{Diagnosed, Report};
use crate::separated_fmt;

/// TODO: add more options
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum Opt {
    #[default]
    Infer,
}

#[derive(Debug, Clone, Default)]
struct FilesDatabase {
    files: Vec<SimpleFile<String, String>>,
}

impl FilesDatabase {
    fn add(&mut self, name: String, source: String) -> usize {
        let cur = self.files.len();
        self.files.push(SimpleFile::new(name, source));
        cur
    }

    fn get(&self, id: usize) -> Result<&SimpleFile<String, String>, files::Error> {
        self.files.get(id).ok_or(files::Error::FileMissing)
    }
}

impl<'a> Files<'a> for FilesDatabase {
    type FileId = usize;

    type Name = &'a str;

    type Source = &'a str;

    fn name(&'a self, id: Self::FileId) -> Result<Self::Name, files::Error> {
        Ok(self.get(id)?.name())
    }

    fn source(&'a self, id: Self::FileId) -> Result<Self::Source, files::Error> {
        Ok(self.get(id)?.source())
    }

    fn line_index(&'a self, id: Self::FileId, byte_index: usize) -> Result<usize, files::Error> {
        self.get(id)?.line_index((), byte_index)
    }

    fn line_range(
        &'a self,
        id: Self::FileId,
        line_index: usize,
    ) -> Result<std::ops::Range<usize>, files::Error> {
        self.get(id)?.line_range((), line_index)
    }
}

struct CompileDuration {
    lex:     Duration,
    parse:   Duration,
    check:   Duration,
    exhaust: Duration,
    total:   Duration,
}

impl Display for CompileDuration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "ran: {:?}", self.total)?;
        writeln!(f, "  lex:     {:?}", self.lex)?;
        writeln!(f, "  parse:   {:?}", self.parse)?;
        writeln!(f, "  check:   {:?}", self.check)?;
        writeln!(f, "  exhaust: {:?}", self.exhaust)?;
        Ok(())
    }
}

type CompileResult<T> = Result<T, Vec<Diagnosed>>;

#[allow(dead_code)]
#[derive(Debug, Clone, Default)]
pub struct Config {
    opt:        Opt,
    input_path: PathBuf,
    bin_path:   PathBuf,
    files:      FilesDatabase,
    max_errors: usize,
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

        let mut files = FilesDatabase::default();

        let input = std::fs::read_to_string(&input_path).expect("Should have valid path as input");
        let input_file_name = input_path
            .file_name()
            .and_then(OsStr::to_str)
            .unwrap_or_default()
            .to_owned();
        Self::add_prelude(&mut files);
        files.add(input_file_name, input);

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
            max_errors: 4,
        }
    }

    fn add_prelude(files: &mut FilesDatabase) {
        use std::fs;

        let dir =
            fs::read_dir("stdlib").expect("Should have standard library in stdlib/ directory");

        for file in dir
            .map(|res| res.expect("Should be valid file"))
            .filter(|file| file.file_type().as_ref().is_ok_and(fs::FileType::is_file))
        {
            let input = std::fs::read_to_string(file.path()).unwrap();
            let name = file.file_name();
            files.add(
                name.into_string().expect("Should be valid unicode string"),
                input,
            );
        }
    }

    fn report(&self, diagnostics: &[Diagnosed]) {
        let config = term::Config::default();
        let writer = StandardStream::stderr(ColorChoice::Auto);

        let mut files = FxHashSet::default();
        {
            let mut writer = writer.lock();
            for err in diagnostics.iter().take(self.max_errors) {
                let _ = term::emit(&mut writer, &config, &self.files, err.diagnostic());
                files.insert(err.id());
            }
        }

        let mut message = String::from("could not compile {");

        let _ = separated_fmt(
            &mut message,
            files
                .into_iter()
                .map(|id| self.files.get(id).unwrap().name()),
            ", ",
            |file, msg| {
                msg.push_str(file);
                Ok(())
            },
        );

        let _ = message.write_fmt(format_args!(
            "}} due to {} previous {} ({} emitted)",
            diagnostics.len(),
            if diagnostics.len() > 1 {
                "error"
            } else {
                "errors"
            },
            self.max_errors.min(diagnostics.len())
        ));

        let error = Diagnostic::error().with_message(message);

        let _ = term::emit(&mut writer.lock(), &config, &self.files, &error);
    }

    fn lex(&self, ctx: &Ctx) -> CompileResult<Vec<Vec<Token>>> {
        let mut tokens = Vec::new();
        let mut errors = Vec::new();

        for (id, file) in self.files.files.iter().enumerate() {
            match Lexer::new(id, file.source()).lex_all() {
                Ok(tk) => tokens.push(tk),
                Err(err) => errors.extend(err.into_iter().map(|err| err.report(ctx))),
            }
        }

        if errors.is_empty() {
            Ok(tokens)
        } else {
            Err(errors)
        }
    }

    fn parse(tokens: Vec<Vec<Token>>, ctx: &Ctx) -> CompileResult<Vec<Module<()>>> {
        let mut parser = Parser::new();
        let mut modules = Vec::new();
        let mut errors = Vec::new();

        for tokens in tokens {
            parser.restart(tokens);
            match parser.parse_all() {
                Ok(parsed) => modules.extend(parsed),
                Err(err) => errors.extend(err.into_iter().map(|err| err.report(ctx))),
            }
        }

        if errors.is_empty() {
            Ok(modules)
        } else {
            Err(errors)
        }
    }

    fn exhaust(modules: &[Module<Ty>], ctx: &Ctx) -> Result<(), Vec<Diagnosed>> {
        let mut errors = Vec::new();
        for module in modules {
            if let Err(err) = check_matches(&module.stmts, ctx) {
                errors.extend(err.into_iter().map(|err| err.report(ctx)));
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    fn compile(&self) -> Result<(Ctx, CompileDuration), Vec<Diagnosed>> {
        let start = Instant::now();

        let ctx = Ctx::default();

        let tokens = self.lex(&ctx)?;

        let end_lex = Instant::now();

        let modules = Self::parse(tokens, &ctx)?;

        let end_parse = Instant::now();

        let mut checker = Checker::with_ctx(ctx);
        let modules = match checker.check_many_modules(modules) {
            Ok(ok) => ok,
            Err(err) => return Err(vec![err.report(checker.ctx())]),
        };

        let end_check = Instant::now();

        Self::exhaust(&modules, checker.ctx())?;

        let end_exhaust = Instant::now();

        let ctx = checker.take_ctx();

        let duration = CompileDuration {
            lex:     end_lex.duration_since(start),
            parse:   end_parse.duration_since(end_lex),
            check:   end_check.duration_since(end_parse),
            exhaust: end_exhaust.duration_since(end_check),
            total:   end_exhaust.duration_since(start),
        };

        Ok((ctx, duration))
    }

    pub fn run(&self) {
        match self.compile() {
            Ok((ctx, duration)) => {
                println!("{ctx}");
                print!("{duration}");
            }
            Err(diagnostics) => self.report(&diagnostics),
        }
    }
}
