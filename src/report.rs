use std::error::Error;
use std::fmt::Write;

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};

use crate::compiler::ctx::{CtxFmt, TypeCtx};
use crate::compiler::error::{InferError, InferErrorKind, MatchNonExhaustive};
use crate::span::Spanned;

impl<T: Error> Spanned<T> {
    pub fn report(&self, input: &str) {
        Report::build(ReportKind::Error, self.span)
            .with_label(Label::new(self.span).with_color(Color::BrightRed))
            .with_message(self.data.to_string())
            .finish()
            .eprint(Source::from(input))
            .unwrap_or_else(|_| unreachable!());
    }
}

impl InferError {
    pub fn report(&self, input: &str) {
        let mut builder = Report::build(ReportKind::Error, self.span());

        match self.kind() {
            InferErrorKind::Uninferable(constr) => {
                match (constr.spans.lhs, constr.spans.rhs) {
                    (None, None) => (),
                    (None, Some(rhs)) => {
                        builder = builder.with_label(
                            Label::new(rhs)
                                .with_color(Color::BrightCyan)
                                .with_message(format!(
                                    "this is of type `{}`",
                                    constr.rhs().fg(Color::BrightCyan)
                                )),
                        );
                    }
                    (Some(lhs), None) => {
                        builder = builder.with_label(
                            Label::new(lhs)
                                .with_color(Color::BrightCyan)
                                .with_message(format!(
                                    "this is of type `{}`",
                                    constr.lhs().fg(Color::BrightCyan)
                                )),
                        );
                    }
                    (Some(lhs), Some(rhs)) => {
                        builder = builder
                            .with_label(Label::new(lhs).with_color(Color::BrightCyan).with_message(
                                format!("this is of type `{}`", constr.lhs().fg(Color::BrightCyan)),
                            ))
                            .with_label(
                                Label::new(rhs).with_color(Color::BrightBlue).with_message(
                                    format!(
                                        "this is of type `{}`",
                                        constr.rhs().fg(Color::BrightBlue)
                                    ),
                                ),
                            );
                    }
                }
                builder = builder.with_message("type mismatch");
            }

            InferErrorKind::Unbound(_) => builder = builder.with_message("undefined variable"),
            InferErrorKind::UnboundModule(_) => builder = builder.with_message("undefined module"),
            InferErrorKind::NotConstructor(_) => builder = builder.with_message("type mismatch"),
            InferErrorKind::Kind(_) => {
                builder = builder
                    .with_message("type mismatch")
                    .with_note("constructor pattern must have kind *");
            }
        }

        builder
            .with_label(Label::new(self.span()).with_message(self.kind().fg(Color::Red)))
            .finish()
            .eprint(Source::from(input))
            .unwrap_or_else(|_| unreachable!());
    }
}

impl MatchNonExhaustive {
    fn fmt_witnesses(&self, ctx: &TypeCtx) -> String {
        let mut out = String::new();
        if self.witnessess().len() > 1 {
            let _ = write!(out, "patterns");
        } else {
            let _ = write!(out, "pattern");
        }
        for w in self.witnessess() {
            let _ = write!(out, " `");
            let _ = w.ctx_fmt(&mut out, ctx);
            let _ = write!(out, "`");
        }
        let _ = write!(out, " not covered");
        out
    }

    pub fn report(&self, ctx: &TypeCtx, input: &str) {
        Report::build(ReportKind::Error, self.span())
            .with_message("non-exhaustive pattern")
            .with_label(
                Label::new(self.span())
                    .with_message(self.fmt_witnesses(ctx))
                    .with_color(Color::Red),
            )
            .finish()
            .eprint(Source::from(input))
            .unwrap_or_else(|_| unreachable!());
    }
}
