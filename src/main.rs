use isa::cli::Config;

fn main() {
    let config = Config::from_env(std::env::args());

    config.run();

    dbg!(isa::global::symbol_count());
}
