use crate::span::Spanned;

pub trait Report {
    fn report(&self, input: &str) -> String;

    fn panic(&self, input: &str) {
        eprintln!("{}", self.report(input));
    }
}

impl<T> Report for Spanned<T>
where
    T: std::error::Error,
{
    fn report(&self, input: &str) -> String {
        let (loc, s) = self.span.start_loc(input);
        format!(
            "error: {}.\nfound at {}: '{}'\n{}\n",
            self.data, loc, &input[self.span], s
        )
    }
}
