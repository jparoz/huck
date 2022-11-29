mod ast;
mod codegen;
mod error;
mod parse;
mod scope;
mod types;

#[allow(dead_code)]
mod utils;

fn main() {
    env_logger::init();

    let filename = std::env::args().nth(1).unwrap();
    let contents = std::fs::read_to_string(&filename).unwrap();

    let lua = utils::transpile(&contents).unwrap_or_else(|e| {
        eprintln!("Compile error: {}", e);
        std::process::exit(1);
    });

    println!("{}", lua);

    eprintln!("\nExecuting...\n");
    eprintln!("{}", utils::execute_lua(&lua));
}
