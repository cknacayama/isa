use std::ffi::OsStr;
use std::fmt::{Debug, Display, Write};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::files::{Files, SimpleFile};
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use codespan_reporting::{files, term};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::compiler::ast::Module;
use crate::compiler::checker::Checker;
use crate::compiler::ctx::Ctx;
use crate::compiler::error::{LexError, MatchNonExhaustive, ParseError};
use crate::compiler::exhaust::check_matches;
use crate::compiler::lexer::Lexer;
use crate::compiler::parser::Parser;
use crate::compiler::token::{Token, TokenKind};
use crate::compiler::types::Ty;
use crate::report::{Report, report_collection};
use crate::separated_fmt;

/// TODO: add more options
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Opt {
    Lex,
    Parse,
    Infer,
    #[default]
    Exhaust,
}

impl Opt {
    #[must_use]
    const fn is_lex(self) -> bool {
        matches!(self, Self::Lex)
    }

    #[must_use]
    const fn is_parse(self) -> bool {
        matches!(self, Self::Parse)
    }

    #[allow(dead_code)]
    #[must_use]
    const fn is_infer(self) -> bool {
        matches!(self, Self::Infer)
    }

    #[must_use]
    const fn is_exhaust(self) -> bool {
        matches!(self, Self::Exhaust)
    }
}

#[derive(Debug, Clone, Default)]
pub struct Config {
    silence:    bool,
    opt:        Opt,
    db:         FilesDatabase,
    max_errors: usize,
}

impl Config {
    #[must_use]
    pub fn from_env(mut env: std::env::Args) -> Self {
        env.next()
            .expect("Should have binary path as first argument");

        let input_path = PathBuf::from(
            env.next()
                .expect("Should have input path as second argument"),
        );

        let mut db = FilesDatabase::default();

        let input = std::fs::read_to_string(&input_path).expect("Should have valid path as input");
        let input_file_name = input_path
            .file_name()
            .and_then(OsStr::to_str)
            .unwrap_or_default()
            .to_owned();
        db.add_prelude();
        db.add(input_file_name, input);

        let opt = env
            .next()
            .and_then(|opt| match opt.as_str() {
                "-l" => Some(Opt::Lex),
                "-p" => Some(Opt::Parse),
                "-i" => Some(Opt::Infer),
                "-e" => Some(Opt::Exhaust),
                _ => None,
            })
            .unwrap_or_default();

        Self {
            silence: false,
            opt,
            db,
            max_errors: 4,
        }
    }

    #[must_use]
    pub fn from_dir(opt: Opt, dir: impl AsRef<Path>) -> Self {
        let mut db = FilesDatabase::default();

        db.add_prelude();
        db.add_dir(dir);

        Self {
            silence: true,
            opt,
            db,
            max_errors: 4,
        }
    }

    fn report<T, I>(&self, diagnostics: I, ctx: &Ctx)
    where
        I: IntoIterator<Item = T>,
        T: Report,
    {
        if self.silence {
            return;
        }

        let mut diagnostics = diagnostics.into_iter();
        let config = term::Config::default();
        let writer = StandardStream::stderr(ColorChoice::Auto);

        let mut files = FxHashSet::default();
        let mut error_count = 0;
        {
            let mut writer = writer.lock();
            for err in report_collection((&mut diagnostics).take(self.max_errors), ctx) {
                let _ = term::emit(&mut writer, &config, &self.db, err.diagnostic());
                files.insert(err.id());
                error_count += 1;
            }
        }

        error_count += diagnostics.count();

        let mut message = String::from("could not compile {");

        let _ = separated_fmt(
            &mut message,
            files.into_iter().map(|id| self.db.get(id).unwrap().name()),
            ", ",
            |file, msg| {
                msg.push_str(file);
                Ok(())
            },
        );

        let _ = message.write_fmt(format_args!(
            "}} due to {} previous {} ({} emitted)",
            error_count,
            if error_count > 1 { "errors" } else { "error" },
            self.max_errors.min(error_count)
        ));

        let error = Diagnostic::error().with_message(message);

        let _ = term::emit(&mut writer.lock(), &config, &self.db, &error);
    }

    fn lex(&self) -> Result<Vec<Token>, Vec<LexError>> {
        let mut folded = Vec::new();
        let mut errs = Vec::new();

        for (id, file) in self.db.files.iter().enumerate() {
            for item in Lexer::new(id, file.source()) {
                match item {
                    Ok(ok) => folded.push(ok),
                    Err(err) => errs.push(err),
                }
            }
        }

        if errs.is_empty() {
            Ok(folded)
        } else {
            Err(errs)
        }
    }

    fn parse(tokens: Vec<Token>) -> Result<Vec<Module<()>>, Vec<ParseError>> {
        Parser::new(tokens).parse_all()
    }

    fn exhaust(modules: &[Module<Ty>], ctx: &Ctx) -> Result<(), Vec<MatchNonExhaustive>> {
        let mut errs = Vec::new();

        for module in modules {
            if let Err(err) = check_matches(&module.stmts, ctx) {
                errs.extend(err);
            }
        }

        if errs.is_empty() { Ok(()) } else { Err(errs) }
    }

    pub fn run(&self) -> Result<(), ()> {
        let ctx = Ctx::default();

        let instants = CompileInstant::default();

        let tokens = self.lex().map_err(|e| self.report(e, &ctx))?;

        let instants = instants.with_lex();
        if self.opt.is_lex() {
            let tokens = Tokens::new(tokens.into_iter().map(|tk| tk.data));
            if !self.silence {
                println!("{tokens}");
                print!("{}", instants.finish());
            }
            return Ok(());
        }

        let modules = Self::parse(tokens).map_err(|e| self.report(e, &ctx))?;

        let instants = instants.with_parse();
        if self.opt.is_parse() {
            if !self.silence {
                println!("parsed {} modules", modules.len());
                print!("{}", instants.finish());
            }
            return Ok(());
        }

        let mut checker = Checker::with_ctx(ctx);
        let modules = checker
            .check_many_modules(modules)
            .map_err(|e| self.report([e], checker.ctx()))?;

        let mut instants = instants.with_check();
        if self.opt.is_exhaust() {
            Self::exhaust(&modules, checker.ctx()).map_err(|e| self.report(e, checker.ctx()))?;
            instants = instants.with_exhaust();
        }

        if !self.silence {
            println!("{}", checker.ctx());
            print!("{}", instants.finish());
        }

        Ok(())
    }
}

#[derive(Debug)]
struct CompileInstant {
    start:   Instant,
    lex:     Option<Instant>,
    parse:   Option<Instant>,
    check:   Option<Instant>,
    exhaust: Option<Instant>,
    end:     Instant,
}

impl Default for CompileInstant {
    fn default() -> Self {
        let now = Instant::now();
        Self {
            start:   now,
            lex:     None,
            parse:   None,
            check:   None,
            exhaust: None,
            end:     now,
        }
    }
}

impl CompileInstant {
    fn with_lex(self) -> Self {
        let now = Instant::now();
        Self {
            lex: Some(now),
            end: now,
            ..self
        }
    }

    fn with_parse(self) -> Self {
        let now = Instant::now();
        Self {
            parse: Some(now),
            end: now,
            ..self
        }
    }

    fn with_check(self) -> Self {
        let now = Instant::now();
        Self {
            check: Some(now),
            end: now,
            ..self
        }
    }

    fn with_exhaust(self) -> Self {
        let now = Instant::now();
        Self {
            exhaust: Some(now),
            end: now,
            ..self
        }
    }

    fn finish(self) -> CompileDuration {
        CompileDuration {
            lex:     self.lex.map(|t| t.duration_since(self.start)),
            parse:   self.parse.map(|t| t.duration_since(self.lex.unwrap())),
            check:   self.check.map(|t| t.duration_since(self.parse.unwrap())),
            exhaust: self.exhaust.map(|t| t.duration_since(self.check.unwrap())),
            total:   self.end.duration_since(self.start),
        }
    }
}

struct CompileDuration {
    lex:     Option<Duration>,
    parse:   Option<Duration>,
    check:   Option<Duration>,
    exhaust: Option<Duration>,
    total:   Duration,
}

impl Display for CompileDuration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "ran: {:?}", self.total)?;
        if let Some(lex) = self.lex {
            writeln!(f, "  lex:     {lex:?}")?;
        }
        if let Some(parse) = self.parse {
            writeln!(f, "  parse:   {parse:?}")?;
        }
        if let Some(check) = self.check {
            writeln!(f, "  check:   {check:?}")?;
        }
        if let Some(exhaust) = self.exhaust {
            writeln!(f, "  exhaust: {exhaust:?}")?;
        }
        Ok(())
    }
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

    fn add_prelude(&mut self) {
        self.add_dir("stdlib");
    }

    fn add_dir(&mut self, dir: impl AsRef<Path>) {
        use std::fs;

        let dir = fs::read_dir(dir).expect("Should be valid directory");

        for file in dir
            .map(|res| res.expect("Should be valid file"))
            .filter(|file| file.file_type().as_ref().is_ok_and(fs::FileType::is_file))
        {
            let input = fs::read_to_string(file.path()).unwrap();
            let name = file.file_name();
            self.add(
                name.into_string().expect("Should be valid unicode string"),
                input,
            );
        }
    }

    fn add_files<'a, I>(&mut self, files: I)
    where
        I: IntoIterator<Item = &'a str>,
    {
        use std::fs;

        for file in files {
            let input = fs::read_to_string(file).expect("Should be valid file path");
            self.add(file.to_owned(), input);
        }
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

struct Tokens(FxHashMap<TokenKind, usize>);

impl Tokens {
    fn new(tokens: impl IntoIterator<Item = TokenKind>) -> Self {
        let mut occ = FxHashMap::default();
        for tk in tokens {
            *occ.entry(tk).or_default() += 1;
        }
        Self(occ)
    }

    fn keyword_count(&self) -> usize {
        self.0
            .iter()
            .filter_map(|(k, v)| if k.is_keyword() { Some(v) } else { None })
            .sum()
    }
}

impl Display for Tokens {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "tokens ({} keywords):", self.keyword_count())?;
        for (tk, count) in &self.0 {
            writeln!(f, "  [{tk}] = {count}")?;
        }

        Ok(())
    }
}
