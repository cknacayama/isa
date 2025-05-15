use std::process::ExitCode;

use isa::driver::Driver;

fn main() -> ExitCode {
    let driver = Driver::new();
    match driver.run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(()) => ExitCode::FAILURE,
    }
}
