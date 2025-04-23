use std::ffi::OsStr;
use std::fmt::Debug;
use std::path::PathBuf;
use std::time::Instant;

use codespan_reporting::files::{Files, SimpleFile};
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use codespan_reporting::{files, term};

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
        Self::add_prelude(&mut files);

        let input = std::fs::read_to_string(&input_path).expect("Should have valid path as input");
        let input_file_name = input_path
            .file_name()
            .and_then(OsStr::to_str)
            .unwrap_or_default()
            .to_owned();
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

    fn report<E>(&self, err: &E, ctx: &Ctx)
    where
        E: Report,
    {
        let writer = StandardStream::stderr(ColorChoice::Auto);
        let config = term::Config::default();
        let diagnostic = err.diagnostic(ctx);

        let _ = term::emit(&mut writer.lock(), &config, &self.files, &diagnostic);
    }

    fn compile(&self) -> bool {
        let start = Instant::now();

        let mut modules = Vec::new();

        for (id, file) in self.files.files.iter().enumerate() {
            let mut parser = Parser::from_input(id, file.source());
            let cur_modules = match parser.parse_all() {
                Ok(expr) if !expr.is_empty() => expr,
                Err(err) => {
                    self.report(&err, &Ctx::default());
                    return true;
                }
                _ => return false,
            };
            modules.extend(cur_modules);
        }

        let mut checker = Checker::default();

        let end_parse = Instant::now();

        let (modules, set) = match checker.check_many_modules(modules) {
            Ok(ok) => ok,
            Err(err) => {
                self.report(&err, checker.ctx());
                return true;
            }
        };

        let end_check = Instant::now();

        for module in modules {
            if let Err(err) = check_matches(&module.stmts, checker.ctx()) {
                self.report(&err, checker.ctx());
                return true;
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

        false
    }

    pub fn run(&self) {
        self.compile();
    }
}
