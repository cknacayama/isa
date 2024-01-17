pub mod ast;
pub mod checker;
pub mod ctx;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod span;
pub mod token;
pub mod types;

use checker::check;
use lexer::lex;
use parser::parse;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::fs::read("in/in.isa")?;

    let tokens = lex(&input)?;

    let (program, arr_sigs, proc_sigs) = parse(&tokens)?;

    let program = check(program, arr_sigs, proc_sigs)?;

    println!("{:#?}", program);

    Ok(())
}
