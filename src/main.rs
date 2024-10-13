use interpreter::interpret;
use parser::parser;
use std::io::Read;
pub mod interpreter;
pub mod parser;

fn main() {
    let mut file = std::fs::File::open("main.lambda").unwrap();
    let mut contents = String::new();
    file.read_to_string(&mut contents).unwrap();
    // 
    match parser(&contents){
        Err(errs) => {
            for err in errs{
                if err.start == err.end{
                    println!("在第{}行第{}列,{}", err.start.line,err.start.column,err.err_info);
                }else{
                    println!("从第{}行第{}列到第{}行第{}列,{}", err.start.line,err.start.column,err.end.line,err.end.column,err.err_info);
                }
               
            }
        }
        Ok(ast) => interpret(ast),
    }
}
