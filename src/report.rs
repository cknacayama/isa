use std::error::Error;
use std::fmt::Write;

use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::compiler::ctx::{Ctx, CtxFmt};
use crate::compiler::error::{DiagnosticLabel, IsaError, MatchNonExhaustive};
use crate::span::Spand;

pub struct Diagnosed {
    id:         usize,
    diagnostic: Diagnostic<usize>,
}

impl From<Diagnosed> for Vec<Diagnosed> {
    fn from(value: Diagnosed) -> Self {
        vec![value]
    }
}

impl Diagnosed {
    pub fn id(&self) -> usize {
        self.id
    }

    pub fn diagnostic(&self) -> &Diagnostic<usize> {
        &self.diagnostic
    }
}

pub trait Report {
    fn file_id(&self) -> usize;
    fn diagnostic(&self, ctx: &Ctx) -> Diagnostic<usize>;

    fn report(&self, ctx: &Ctx) -> Diagnosed {
        Diagnosed {
            id:         self.file_id(),
            diagnostic: self.diagnostic(ctx),
        }
    }
}

impl<T: Error> Report for Spand<T> {
    fn file_id(&self) -> usize {
        self.span.file_id()
    }

    fn diagnostic(&self, _: &Ctx) -> Diagnostic<usize> {
        Diagnostic::error()
            .with_message(self.data())
            .with_label(Label::primary(self.span.file_id(), self.span))
    }
}

impl Report for IsaError {
    fn file_id(&self) -> usize {
        self.primary_label().span().file_id()
    }

    fn diagnostic(&self, _: &Ctx) -> Diagnostic<usize> {
        Diagnostic::error()
            .with_message(self.message())
            .with_label(self.primary_label().as_primary())
            .with_labels_iter(self.labels().iter().map(DiagnosticLabel::as_secondary))
            .with_notes_iter(self.note().map(String::from))
    }
}

impl MatchNonExhaustive {
    fn fmt_witnesses(&self, ctx: &Ctx) -> String {
        let mut out = String::new();
        if self.witnessess().len() > 1 {
            let _ = write!(out, "patterns");
        } else {
            let _ = write!(out, "pattern");
        }
        let mut first = true;
        for w in self.witnessess() {
            if first {
                first = false;
            } else {
                let _ = write!(out, ",");
            }
            let _ = write!(out, " `");
            let _ = w.ctx_fmt(&mut out, ctx);
            let _ = write!(out, "`");
        }
        let _ = write!(out, " not covered");
        out
    }
}

impl Report for MatchNonExhaustive {
    fn file_id(&self) -> usize {
        self.span().file_id()
    }

    fn diagnostic(&self, ctx: &Ctx) -> Diagnostic<usize> {
        Diagnostic::error()
            .with_message("non-exhaustive pattern")
            .with_label(
                Label::primary(self.span().file_id(), self.span())
                    .with_message(self.fmt_witnesses(ctx)),
            )
    }
}
