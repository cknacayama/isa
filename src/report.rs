use std::error::Error;
use std::fmt::Write;

use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::compiler::ctx::{CtxFmt, TypeCtx};
use crate::compiler::error::{IsaError, MatchNonExhaustive};
use crate::span::Spanned;

pub trait Report {
    fn diagnostic(&self, file_id: usize, ctx: &TypeCtx) -> Diagnostic<usize>;
}

impl<T: Error> Report for Spanned<T> {
    fn diagnostic(&self, file_id: usize, _: &TypeCtx) -> Diagnostic<usize> {
        Diagnostic::error()
            .with_message(self.data())
            .with_label(Label::primary(file_id, self.span))
    }
}

impl Report for IsaError {
    fn diagnostic(&self, file_id: usize, _: &TypeCtx) -> Diagnostic<usize> {
        Diagnostic::error()
            .with_message(self.message())
            .with_label(self.primary_label().as_primary(file_id))
            .with_labels_iter(self.labels().iter().map(|l| l.as_secondary(file_id)))
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
}

impl Report for MatchNonExhaustive {
    fn diagnostic(&self, file_id: usize, ctx: &TypeCtx) -> Diagnostic<usize> {
        Diagnostic::error()
            .with_message("non-exhaustive pattern")
            .with_label(Label::primary(file_id, self.span()).with_message(self.fmt_witnesses(ctx)))
    }
}
