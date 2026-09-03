use std::env;

use syntax::functions::CheckedProgram;

enum CompilerError {
    CouldNotReadFile(String),
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("Please provide a file to compile.");
        return;
    }
    let program = match get_program_from_file(&args[1]) {
        Ok(program) => program,
        Err(e) => {
            match e {
                CompilerError::CouldNotReadFile(s) => {
                    println!("Error reading file: {}", s);
                }
            }
            std::process::exit(1);
        }
    };
}

fn get_program_from_file(file_path: &str) -> Result<CheckedProgram, CompilerError> {
    let ast = std::fs::read_to_string(&file_path)
        .map_err(|e| CompilerError::CouldNotReadFile(e.to_string()))?;
    let program: CheckedProgram =
        serde_json::from_str(&ast).map_err(|e| CompilerError::CouldNotReadFile(e.to_string()))?;
    Ok(program)
}
