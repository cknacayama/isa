use std::process::ExitCode;

use isa::driver::Config;

fn main() -> ExitCode {
    let config = Config::from_env(std::env::args());
    match config.run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(()) => ExitCode::FAILURE,
    }
}
