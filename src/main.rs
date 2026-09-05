use inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, StructType},
    values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue},
};
use std::collections::HashMap;
use std::env;
use syntax::{
    ast::{Expression, Statement},
    functions::{CheckedProgram, Function, FunctionId, FunctionImplementation},
    types::{Type, Value},
};

struct CodeGenerator<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,

    functions: HashMap<FunctionId, FunctionValue<'ctx>>,
    variables: Vec<HashMap<String, PointerValue<'ctx>>>,

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
            variables: vec![HashMap::new()],
            string_type: context.struct_type(
                &[
                    context.ptr_type(AddressSpace::default()).into(),
                    context.i64_type().into(),
                ],
                false,
            ),
        }
    }

    fn push_scope(&mut self) {
        self.variables.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.variables.pop();
    }

    fn add_variable(&mut self, name: String, val: PointerValue<'ctx>) {
        self.variables
            .last_mut()
            .expect("ran out of scopes")
            .insert(name, val);
    }

    fn get_variable(&self, name: &String) -> &PointerValue<'ctx> {
        self.variables
            .iter()
            .rev()
            .find_map(|v| v.get(name))
            .expect("failed to get variable")
    }

    fn current_block_has_terminator(&self) -> bool {
        self.builder
            .get_insert_block()
            .expect("failed to get insert block")
            .get_terminator()
            .is_some()
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

    fn compile_function(&mut self, function: &Function) -> Result<(), CompilerError> {
        let FunctionImplementation::Oxide(body) = &function.implementation else {
            println!(
                "cannot compile function {}: only Oxide functions can be compiled",
                function.signature.name
            );
            return Ok(());
        };

        let llvm_function = self
            .functions
            .get(&function.id)
            .expect(format!("function {} was not declared", function.signature.name).as_str());

        let entry = self.context.append_basic_block(*llvm_function, "entry");

        self.builder.position_at_end(entry);

        for statement in &body.statements {
            self.compile_statement(statement)?;
        }

        if !self.current_block_has_terminator() {
            if function.signature.return_type == Type::Unit {
                self.builder
                    .build_return(None)
                    .expect("failed to built void return");
            } else {
                panic!("Missing return statement in non unit type function");
            }
        }

        Ok(())
    }

    fn compile_statement(&mut self, statement: &Statement) -> Result<(), CompilerError> {
        let function = self
            .builder
            .get_insert_block()
            .expect("failed to get insert block")
            .get_parent()
            .expect("failed to get parent block");

        match statement {
            Statement::Let { .. } => self.compile_let(statement)?,
            Statement::Assignment { .. } => self.compile_assignment(statement)?,
            Statement::If { .. } => self.compile_if(statement, &function)?,
            Statement::While { .. } => self.compile_while(statement, &function)?,
            Statement::For { .. } => self.compile_for(statement, &function)?,
            Statement::Scope { .. } => self.compile_scope(statement)?,
            Statement::ExpressionStatement { expression } => {
                self.compile_expression(expression)?;
            }
            Statement::Return { .. } => self.compile_return(statement)?,
            Statement::Break => todo!(),    // uhh
            Statement::Continue => todo!(), // uhh
            Statement::FunctionDefinition { .. } => {
                unreachable!("Function definitions should be declared before compilation")
            }
            Statement::Pass => {
                unreachable!("Pass statements should be not be present in the checked program")
            }
        }
        Ok(())
    }

    fn compile_let(&mut self, statement: &Statement) -> Result<(), CompilerError> {
        let Statement::Let {
            identifier,
            expression,
            mutable: _,
            var_type,
        } = statement
        else {
            return Err(CompilerError::WrongStatementType(
                "Let".into(),
                format!("{:?}", statement),
            ));
        };

        let llvm_type = self.llvm_type(
            &var_type.expect(format!("unknown type of variable {}", identifier).as_str()),
        );
        let initialiser = self.const_expression(expression);
        let alloca = self
            .builder
            .build_alloca(llvm_type, identifier)
            .expect("failed to build alloca");
        self.builder
            .build_store(alloca, initialiser)
            .expect("failed to build store");
        self.add_variable(identifier.clone(), alloca);

        Ok(())
    }

    fn compile_assignment(&mut self, statement: &Statement) -> Result<(), CompilerError> {
        let Statement::Assignment {
            identifier,
            expression,
        } = statement
        else {
            return Err(CompilerError::WrongStatementType(
                "Assignment".into(),
                format!("{:?}", statement),
            ));
        };

        let alloca = self.get_variable(identifier);
        let value = self.const_expression(expression);
        self.builder
            .build_store(*alloca, value)
            .expect("failed to build store");

        Ok(())
    }

    fn compile_if(
        &mut self,
        statement: &Statement,
        function: &FunctionValue,
    ) -> Result<(), CompilerError> {
        let Statement::If {
            condition,
            body,
            else_block,
        } = statement
        else {
            return Err(CompilerError::WrongStatementType(
                "If".into(),
                format!("{:?}", statement),
            ));
        };

        let condition_value = self.const_expression(condition);

        let then_block = self.context.append_basic_block(*function, "then");
        let else_llvm_block = self.context.append_basic_block(*function, "else");
        let merge_block = self.context.append_basic_block(*function, "merge");

        self.builder
            .build_conditional_branch(
                condition_value.into_int_value(),
                then_block,
                else_llvm_block,
            )
            .expect("failed to build conditional branch");

        self.builder.position_at_end(then_block);
        for statement in body {
            self.compile_statement(statement)?;
        }
        if !self.current_block_has_terminator() {
            self.builder
                .build_unconditional_branch(merge_block)
                .expect("failed to build unconditional branch");
        }

        self.builder.position_at_end(else_llvm_block);
        if let Some(else_statements) = else_block {
            for statement in else_statements {
                self.compile_statement(statement)?;
            }
        }
        if !self.current_block_has_terminator() {
            self.builder
                .build_unconditional_branch(merge_block)
                .expect("failed to build unconditional branch");
        }

        self.builder.position_at_end(merge_block);

        Ok(())
    }

    fn compile_while(
        &mut self,
        statement: &Statement,
        function: &FunctionValue,
    ) -> Result<(), CompilerError> {
        let Statement::While { condition, body } = statement else {
            return Err(CompilerError::WrongStatementType(
                "While".into(),
                format!("{:?}", statement),
            ));
        };
        let condition_value = self.const_expression(condition);

        let check_block = self.context.append_basic_block(*function, "check");
        let then_block = self.context.append_basic_block(*function, "then");
        let merge_block = self.context.append_basic_block(*function, "merge");

        self.builder.position_at_end(check_block);

        self.builder
            .build_conditional_branch(condition_value.into_int_value(), then_block, merge_block)
            .expect("failed to build conditional branch");
        self.builder.position_at_end(then_block);
        for statement in body {
            self.compile_statement(statement)?;
        }
        if !self.current_block_has_terminator() {
            self.builder
                .build_unconditional_branch(check_block)
                .expect("failed to build unconditional branch to while check");
        }
        self.builder.position_at_end(merge_block);
        Ok(())
    }

    fn compile_for(
        &mut self,
        statement: &Statement,
        function: &FunctionValue,
    ) -> Result<(), CompilerError> {
        let Statement::For {
            initialiser,
            condition,
            increment,
            body,
        } = statement
        else {
            return Err(CompilerError::WrongStatementType(
                "For".into(),
                format!("{:?}", statement),
            ));
        };

        if let Some(init) = initialiser {
            self.compile_statement(init)?;
        }

        let check_block = self.context.append_basic_block(*function, "check");
        let then_block = self.context.append_basic_block(*function, "then");
        let merge_block = self.context.append_basic_block(*function, "merge");
        self.builder.position_at_end(check_block);
        if let Some(cond) = condition {
            self.builder
                .build_conditional_branch(
                    self.const_expression(cond).into_int_value(),
                    then_block,
                    merge_block,
                )
                .expect("failed to build conditional branch in for");
        } else {
            self.builder
                .build_unconditional_branch(then_block)
                .expect("failed to build unconditional branch in for");
        }
        self.builder.position_at_end(then_block);
        for statement in body {
            self.compile_statement(statement)?;
        }
        if let Some(inc) = increment {
            self.compile_statement(inc)?;
        }
        if !self.current_block_has_terminator() {
            self.builder
                .build_unconditional_branch(check_block)
                .expect("failed to build unconditional branch to check block in for");
        }
        self.builder.position_at_end(merge_block);
        Ok(())
    }

    fn compile_scope(&mut self, statement: &Statement) -> Result<(), CompilerError> {
        let Statement::Scope { body } = statement else {
            return Err(CompilerError::WrongStatementType(
                "Scope".into(),
                format!("{:?}", statement),
            ));
        };
        self.push_scope();
        for statement in body {
            self.compile_statement(statement)?;
        }
        self.pop_scope();
        Ok(())
    }

    fn compile_return(&mut self, statement: &Statement) -> Result<(), CompilerError> {
        let Statement::Return { value } = statement else {
            return Err(CompilerError::WrongStatementType(
                "Return".into(),
                format!("{:?}", statement),
            ));
        };

        let ret_val = if let Some(val) = value {
            Some(self.const_expression(val))
        } else {
            None
        };
        match ret_val {
            Some(val) => {
                self.builder.build_return(Some(&val)).expect("grr");
            }
            None => {
                self.builder.build_return(None).expect("grr but none");
            }
        }
        Ok(())
    }

    fn compile_expression(
        &mut self,
        expression: &Expression,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match expression {
            Expression::Literal(_) => Ok(self.const_expression(expression)),
            Expression::Identifier(name) => Ok(self.get_variable(name).as_basic_value_enum()),
            Expression::BinaryOp {
                left,
                operator,
                right,
            } => todo!(),
            Expression::UnaryOp { operator, operand } => todo!(),
            Expression::ResolvedFunctionCall {
                function_id,
                arguments,
            } => todo!(),
            Expression::UnresolvedFunctionCall { .. } => {
                unreachable!("unresolve function call reached compiler")
            }
        }
    }
}

#[derive(Debug)]
enum CompilerError {
    WrongStatementType(String, String),
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
                _ => unreachable!("unexpected error when reading from file."),
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
    let mut code_gen = CodeGenerator::new(&context, &program_name);

    declare_all_functions(&mut code_gen, &program);

    declare_global_variables(&code_gen, &program);

    compile_all_functions(&mut code_gen, &program);

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
                unreachable!("Global variable is not a let statement");
            }
        }
    }
}

fn declare_all_functions(code_gen: &mut CodeGenerator, program: &CheckedProgram) {
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
        let function_value = code_gen
            .module
            .add_function(&function_name, function_type, None);
        code_gen
            .functions
            .insert(function.id.clone(), function_value);
    }
}

fn compile_all_functions(code_gen: &mut CodeGenerator, program: &CheckedProgram) {
    for function in &program.function_table.functions {
        // only compile user defined functions, builtins will be linked later
        if matches!(function.implementation, FunctionImplementation::Oxide(_)) {
            code_gen
                .compile_function(function)
                .expect("failed to compile function");
        }
    }
}
