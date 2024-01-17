pub mod ast;
pub mod checker;
pub mod ctx;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod span;
pub mod token;
pub mod types;

use checker::Checker;
use lexer::Lexer;
use parser::Parser;

fn main() {
    let input = std::fs::read("in/in.isa").unwrap();

    let mut lexer = Lexer::new(&input);
    let tokens = match lexer.lex() {
        Ok(tokens) => tokens,
        Err(e) => {
            eprintln!("{}", e);
            return;
        }
    };

    let mut parser = Parser::new(&tokens);

    let program = match parser.parse() {
        Ok(program) => program,
        Err(e) => {
            eprintln!("{}", e);
            return;
        }
    };

    let mut checker = Checker::new();

    let program = match checker.check(program) {
        Ok(program) => program,
        Err(e) => {
            eprintln!("{}", e);
            return;
        }
    };

    println!("{:#?}", program);
}
