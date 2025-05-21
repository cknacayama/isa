mod cli;

use std::fmt::{Debug, Display, Write};
use std::io::Read;
use std::path::Path;
use std::time::{Duration, Instant};

use cli::{Cli, Command};
use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::files::{Files, SimpleFile};
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use codespan_reporting::{files, term};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::comma_fmt;
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

pub struct Driver {
    db: FilesDatabase,

    quiet:      bool,
    command:    Command,
    max_errors: usize,
}

impl Default for Driver {
    fn default() -> Self {
        Self::new()
    }
}

impl Driver {
    #[must_use]
    pub fn new() -> Self {
        Self::from_config(&<Cli as clap::Parser>::parse())
    }

    fn read_stdin() -> String {
        let mut input = String::new();
        std::io::stdin()
            .read_to_string(&mut input)
            .expect("Should read input from stdin");
        input
    }

    #[must_use]
    fn from_config(cfg: &Cli) -> Self {
        let command = cfg.command.unwrap_or_default();

        let mut db = FilesDatabase::default();

        if cfg.stdin {
            db.add("<stdin>", Self::read_stdin());
        }
        if command >= Command::Infer {
            db.add_prelude();
        }

        db.add_files(cfg.files.iter());

        Self {
            db,
            command,
            quiet: cfg.quiet,
            max_errors: cfg.max_errors,
        }
    }

    fn report<T, I>(&self, diagnostics: I, ctx: &Ctx)
    where
        I: IntoIterator<Item = T>,
        T: Report,
    {
        if self.quiet {
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

        let _ = comma_fmt(
            &mut message,
            files.into_iter().map(|id| self.db.get(id).unwrap().name()),
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
        if self.command.is_lex() {
            let tokens = Tokens::new(tokens.into_iter().map(|tk| tk.data));
            if !self.quiet {
                println!("{tokens}");
                print!("{}", instants.finish());
            }
            return Ok(());
        }

        let modules = Self::parse(tokens).map_err(|e| self.report(e, &ctx))?;

        let instants = instants.with_parse();
        if self.command.is_parse() {
            if !self.quiet {
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
        if self.command.is_exhaust() {
            Self::exhaust(&modules, checker.ctx()).map_err(|e| self.report(e, checker.ctx()))?;
            instants = instants.with_exhaust();
        }

        if !self.quiet {
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
    #[allow(clippy::needless_pass_by_value)]
    fn add(&mut self, name: impl ToString, source: String) -> usize {
        let cur = self.files.len();
        self.files.push(SimpleFile::new(name.to_string(), source));
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
            self.add(name.display(), input);
        }
    }

    fn add_files<I, P>(&mut self, files: I)
    where
        I: IntoIterator<Item = P>,
        P: AsRef<Path>,
    {
        use std::fs;

        for file in files {
            let path = file.as_ref();
            let input = fs::read_to_string(path).expect("Should be valid file path");
            let name = path.file_name().unwrap().to_str().unwrap();
            self.add(name, input);
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

#[derive(Default)]
struct Tokens {
    simple:    FxHashMap<String, usize>,
    idents:    usize,
    operators: usize,
    integers:  usize,
    reals:     usize,
    chars:     usize,
    strings:   usize,
}

impl Tokens {
    fn new(tokens: impl IntoIterator<Item = TokenKind>) -> Self {
        let mut tks = Self::default();
        for tk in tokens {
            match tk {
                TokenKind::Integer(_) => tks.integers += 1,
                TokenKind::Real(_) => tks.reals += 1,
                TokenKind::Ident(_) => tks.idents += 1,
                TokenKind::Char(_) => tks.chars += 1,
                TokenKind::String(_) => tks.strings += 1,
                TokenKind::Operator(_) => tks.operators += 1,
                _ => *tks.simple.entry(tk.to_string()).or_default() += 1,
            }
        }
        tks
    }
}

impl Display for Tokens {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "tokens:")?;
        writeln!(f, "  idents: {}", self.idents)?;
        writeln!(f, "  strings: {}", self.strings)?;
        writeln!(f, "  chars: {}", self.chars)?;
        writeln!(f, "  integers: {}", self.integers)?;
        writeln!(f, "  reals: {}", self.reals)?;
        writeln!(f, "  operators: {}", self.operators)?;
        for (tk, count) in &self.simple {
            writeln!(f, "  [{tk}] = {count}")?;
        }

        Ok(())
    }
}
