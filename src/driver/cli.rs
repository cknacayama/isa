use clap::builder::styling::{AnsiColor, Effects, Style, Styles};

#[derive(clap::Parser, Debug, Clone, Default)]
#[clap(styles = CARGO_STYLING)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Option<Command>,

    pub files: Vec<String>,

    /// Do not print log messages
    #[arg(short, long, default_value_t = false)]
    pub quiet: bool,

    /// Read input from stdin
    #[arg(long, default_value_t = false)]
    pub stdin: bool,

    /// Maximum amount of errors to report
    #[arg(long, value_name = "max-errors", default_value_t = 4)]
    pub max_errors: usize,
}

#[derive(clap::Subcommand, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Command {
    /// Only lex files
    Lex,
    /// Only parse files
    Parse,
    /// Only infer/check program types
    Infer,
    /// Run all passes, including pattern exhaustiveness analysis
    #[default]
    Exhaust,
}

impl Command {
    #[must_use]
    pub const fn is_lex(self) -> bool {
        matches!(self, Self::Lex)
    }

    #[must_use]
    pub const fn is_parse(self) -> bool {
        matches!(self, Self::Parse)
    }

    #[must_use]
    pub const fn is_exhaust(self) -> bool {
        matches!(self, Self::Exhaust)
    }
}

const HEADER: Style = AnsiColor::Green.on_default().effects(Effects::BOLD);
const USAGE: Style = AnsiColor::Green.on_default().effects(Effects::BOLD);
const LITERAL: Style = AnsiColor::Cyan.on_default().effects(Effects::BOLD);
const PLACEHOLDER: Style = AnsiColor::Cyan.on_default();
const ERROR: Style = AnsiColor::Red.on_default().effects(Effects::BOLD);
const VALID: Style = AnsiColor::Cyan.on_default().effects(Effects::BOLD);
const INVALID: Style = AnsiColor::Yellow.on_default().effects(Effects::BOLD);

/// Cargo's color style
/// [source](https://github.com/crate-ci/clap-cargo/blob/master/src/style.rs)
const CARGO_STYLING: Styles = Styles::styled()
    .header(HEADER)
    .usage(USAGE)
    .literal(LITERAL)
    .placeholder(PLACEHOLDER)
    .error(ERROR)
    .valid(VALID)
    .invalid(INVALID);
