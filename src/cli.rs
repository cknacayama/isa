use std::ffi::OsStr;
use std::fmt::{Debug, Display};
use std::path::PathBuf;
use std::time::{Duration, Instant};

use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::files::{Files, SimpleFile};
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use codespan_reporting::{files, term};

use crate::compiler::ast::Module;
use crate::compiler::checker::Checker;
use crate::compiler::ctx::Ctx;
use crate::compiler::exhaust::check_matches;
use crate::compiler::lexer::{LexResult, Lexer};
use crate::compiler::parser::{ParseResult, Parser};
use crate::compiler::token::Token;
use crate::report::Report;

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

#[allow(dead_code)]
#[derive(Debug, Clone, Default)]
pub struct Config {
    opt:        Opt,
    input_path: PathBuf,
    bin_path:   PathBuf,
    files:      FilesDatabase,
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

    fn report(&self, id: usize, diagnostic: &Diagnostic<usize>) {
        let writer = StandardStream::stderr(ColorChoice::Auto);
        let config = term::Config::default();

        let _ = term::emit(&mut writer.lock(), &config, &self.files, diagnostic);

        let file_name = self.files.get(id).unwrap().name();
        let error = Diagnostic::error().with_message(format!(
            "could not compile `{file_name}` due to previous error"
        ));

        let _ = term::emit(&mut writer.lock(), &config, &self.files, &error);
    }

    fn lex(&self) -> LexResult<Vec<Vec<Token>>> {
        self.files
            .files
            .iter()
            .enumerate()
            .map(|(id, file)| Lexer::new(id, file.source()).collect())
            .collect()
    }

    fn parse(&self, tokens: Vec<Vec<Token>>) -> ParseResult<Vec<Module<()>>> {
        let mut parser = Parser::new();
        let mut modules = Vec::new();

        for tokens in tokens {
            parser.restart(tokens);
            let parsed = parser.parse_all()?;
            modules.extend(parsed);
        }

        Ok(modules)
    }

    fn compile(&self) -> Result<(Ctx, CompileDuration), (usize, Diagnostic<usize>)> {
        let start = Instant::now();

        let tokens = match self.lex() {
            Ok(tokens) => tokens,
            Err(err) => return Err(err.report(&Ctx::default())),
        };

        let end_lex = Instant::now();

        let modules = match self.parse(tokens) {
            Ok(modules) => modules,
            Err(err) => return Err(err.report(&Ctx::default())),
        };

        let end_parse = Instant::now();

        let mut checker = Checker::default();
        let modules = match checker.check_many_modules(modules) {
            Ok(ok) => ok,
            Err(err) => return Err(err.report(checker.ctx())),
        };

        let end_check = Instant::now();

        for module in modules {
            check_matches(&module.stmts, checker.ctx()).map_err(|err| err.report(checker.ctx()))?;
        }

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
            Err((id, diagnostic)) => self.report(id, &diagnostic),
        }
    }
}
