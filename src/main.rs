#![allow(dead_code)]
pub mod ast;
pub mod ctx;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod token;
pub mod types;

use lexer::Lexer;
use parser::Parser;

fn main() {
    let input = include_bytes!("../in/in.isa");

    let tokens = match Lexer::new(input).lex() {
        Ok(tokens) => tokens,
        Err(err) => {
            eprintln!("{}", err);
            return;
        }
    };

    let ast = match Parser::new(&tokens).parse() {
        Ok(ast) => ast,
        Err(err) => {
            eprintln!("{}", err);
            return;
        }
    };

    println!("{:#?}", ast);
}
