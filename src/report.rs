use std::error::Error;
use std::fmt::Write;

use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::compiler::ctx::{CtxFmt, TypeCtx};
use crate::compiler::error::{InferError, InferErrorKind, MatchNonExhaustive};
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

impl Report for InferError {
    fn diagnostic(&self, file_id: usize, _: &TypeCtx) -> Diagnostic<usize> {
        let mut diagnostic = Diagnostic::error();

        let primary_span = match self.kind() {
            InferErrorKind::Uninferable(constr) => {
                diagnostic = diagnostic.with_message("type mismatch");
                match constr.spans.sub_exprs {
                    None => self.span(),
                    Some((None, rhs)) => rhs,
                    Some((Some(lhs), rhs)) => {
                        diagnostic = diagnostic
                            .with_label(
                                Label::secondary(file_id, lhs)
                                    .with_message(format!("this is of type `{}`", constr.lhs())),
                            )
                            .with_label(
                                Label::secondary(file_id, rhs)
                                    .with_message(format!("this is of type `{}`", constr.rhs())),
                            );
                        rhs
                    }
                }
            }

            InferErrorKind::Unbound(_) => {
                diagnostic = diagnostic.with_message("undefined variable");
                self.span()
            }
            InferErrorKind::UnboundModule(_) => {
                diagnostic = diagnostic.with_message("undefined module");
                self.span()
            }
            InferErrorKind::NotConstructor(_) => {
                diagnostic = diagnostic.with_message("type mismatch");
                self.span()
            }
            InferErrorKind::Kind(_) => {
                diagnostic = diagnostic
                    .with_message("type mismatch")
                    .with_note("constructor pattern must have kind *");
                self.span()
            }
        };

        diagnostic.with_label(Label::primary(file_id, primary_span).with_message(self.kind()))
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
