use isa::driver::Config;

fn main() {
    let config = Config::from_env(std::env::args());
    config.run();
}
