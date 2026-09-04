use inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, StructType},
    values::{BasicValueEnum, FunctionValue, PointerValue},
};
use std::collections::HashMap;
use std::env;
use syntax::{
    ast::{Expression, Statement},
    functions::CheckedProgram,
    types::{Type, Value},
};

struct CodeGenerator<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,

    functions: HashMap<String, FunctionValue<'ctx>>,
    variables: HashMap<String, PointerValue<'ctx>>,

    string_type: StructType<'ctx>,
}
impl<'ctx> CodeGenerator<'ctx> {
    fn new(context: &'ctx Context, program_name: &str) -> CodeGenerator<'ctx> {
        let module = context.create_module(program_name);
        let builder = context.create_builder();
        CodeGenerator {
            context,
            module,
            builder,
            functions: HashMap::new(),
            variables: HashMap::new(),
            string_type: context.struct_type(
                &[
                    context.ptr_type(AddressSpace::default()).into(),
                    context.i64_type().into(),
                ],
                false,
            ),
        }
    }

    fn llvm_type(&self, ty: &Type) -> BasicTypeEnum<'ctx> {
        match ty {
            Type::I8 | Type::U8 => self.context.i8_type().into(),
            Type::I16 | Type::U16 => self.context.i16_type().into(),
            Type::I32 | Type::U32 => self.context.i32_type().into(),
            Type::I64 | Type::U64 => self.context.i64_type().into(),
            Type::F32 => self.context.f32_type().into(),
            Type::F64 => self.context.f64_type().into(),
            Type::Bool => self.context.bool_type().into(),
            Type::String => self.string_type.into(),
            Type::Unit => panic!("Unit type should only be used as a return type"),
        }
    }

    fn const_expression(&self, expr: &Expression) -> BasicValueEnum<'ctx> {
        match expr {
            Expression::Literal(literal) => match literal {
                Value::Number(number) => match number {
                    syntax::types::Number::I8(n) => {
                        self.context.i8_type().const_int(*n as u64, false).into()
                    }
                    syntax::types::Number::I16(n) => {
                        self.context.i16_type().const_int(*n as u64, false).into()
                    }
                    syntax::types::Number::I32(n) => {
                        self.context.i32_type().const_int(*n as u64, false).into()
                    }
                    syntax::types::Number::I64(n) => {
                        self.context.i64_type().const_int(*n as u64, false).into()
                    }
                    syntax::types::Number::U8(n) => {
                        self.context.i8_type().const_int(*n as u64, false).into()
                    }
                    syntax::types::Number::U16(n) => {
                        self.context.i16_type().const_int(*n as u64, false).into()
                    }
                    syntax::types::Number::U32(n) => {
                        self.context.i32_type().const_int(*n as u64, false).into()
                    }
                    syntax::types::Number::U64(n) => {
                        self.context.i64_type().const_int(*n as u64, false).into()
                    }
                    syntax::types::Number::F32(n) => {
                        self.context.f32_type().const_float(*n as f64).into()
                    }
                    syntax::types::Number::F64(n) => self.context.f64_type().const_float(*n).into(),
                    syntax::types::Number::IntegerLiteral(_)
                    | syntax::types::Number::FloatLiteral(_) => unreachable!(
                        "number literals should be converted to specific types during type checking"
                    ),
                },
                Value::String(value) => {
                    let string_ptr = self
                        .builder
                        .build_global_string_ptr(value, "string")
                        .expect("builder error");
                    let string_len = self.context.i64_type().const_int(value.len() as u64, false);
                    let string_struct = self.string_type.const_named_struct(&[
                        string_ptr.as_pointer_value().into(),
                        string_len.into(),
                    ]);
                    string_struct.into()
                }
                Value::Bool(b) => self.context.bool_type().const_int(*b as u64, false).into(),
                Value::Unit => panic!("Unit type should only be used as a return type"),
            },
            _ => panic!("Global variables can only be initialized with constant expressions."),
        }
    }
}
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

    let program_name = String::from(
        args[1]
            .split('.')
            .nth(0)
            .expect("error finding program name"),
    );
    let context = Context::create();
    let code_gen = CodeGenerator::new(&context, &program_name);

    declare_all_functions(&code_gen, &program);

    declare_global_variables(&code_gen, &program);

    println!("{}", code_gen.module.print_to_string().to_string());
}

fn get_program_from_file(file_path: &str) -> Result<CheckedProgram, CompilerError> {
    let ast = std::fs::read_to_string(&file_path)
        .map_err(|e| CompilerError::CouldNotReadFile(e.to_string()))?;
    let program: CheckedProgram =
        serde_json::from_str(&ast).map_err(|e| CompilerError::CouldNotReadFile(e.to_string()))?;
    Ok(program)
}

fn declare_global_variables(code_gen: &CodeGenerator, program: &CheckedProgram) {
    for variable in &program.globals {
        match variable {
            Statement::Let {
                identifier,
                expression,
                mutable: _,
                var_type,
            } => {
                let llvm_type = code_gen
                    .llvm_type(&var_type.expect(
                        format!("unknown type of global variable {}", identifier).as_str(),
                    ));
                let initialiser = code_gen.const_expression(expression);
                let global_variable = code_gen.module.add_global(llvm_type, None, &identifier);
                global_variable.set_initializer(&initialiser);
            }
            _ => {
                panic!("Global variable is not a let statement");
            }
        }
    }
}

fn declare_all_functions(code_gen: &CodeGenerator, program: &CheckedProgram) {
    for function in &program.function_table.functions {
        let param_types: &Vec<BasicMetadataTypeEnum> = &function
            .signature
            .parameters
            .iter()
            .map(|param_type| code_gen.llvm_type(param_type).into())
            .collect::<Vec<BasicMetadataTypeEnum>>();
        let function_type = match &function.signature.return_type {
            Type::Unit => code_gen.context.void_type().fn_type(param_types, false),
            _ => code_gen
                .llvm_type(&function.signature.return_type)
                .fn_type(&param_types, false),
        };
        // Create a unique function name by appending the function ID to the original name
        // eg print_1()
        let function_name = format!("{}_{}", function.signature.name, function.id.0);
        code_gen
            .module
            .add_function(&function_name, function_type, None);
    }
}
