use interpreter::interpret;
use parser::parse;
use scanner::scan;
use std::io::Read;
pub mod interpreter;
pub mod parser;
pub mod scanner;

fn main() {
    let mut file = std::fs::File::open("main.lambda").unwrap();
    let mut contents = String::new();
    file.read_to_string(&mut contents).unwrap();
    let mut tokens = scan(contents);
    let ast = parse(&mut tokens);
    interpret(ast);
}
