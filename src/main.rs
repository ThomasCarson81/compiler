use inkwell::{
    AddressSpace, FloatPredicate, IntPredicate, OptimizationLevel,
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::Module,
    targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine},
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, StructType},
    values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, PointerValue},
};
use std::{collections::HashMap, str};
use std::{env, path::Path};
use syntax::{
    ast::{Expression, Statement},
    functions::{CheckedProgram, Function, FunctionId, FunctionImplementation},
    tokens::TokenType,
    types::{Type, Value},
};

struct Variable<'ctx> {
    ptr: PointerValue<'ctx>,
    ty: BasicTypeEnum<'ctx>,
}

struct LoopContext<'ctx> {
    break_target: BasicBlock<'ctx>,
    continue_target: BasicBlock<'ctx>,
}

struct CodeGenerator<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,

    functions: HashMap<FunctionId, FunctionValue<'ctx>>,
    variables: Vec<HashMap<String, Variable<'ctx>>>,
    loop_stack: Vec<LoopContext<'ctx>>,

    string_type: StructType<'ctx>,
    string_concat_fn: FunctionValue<'ctx>,
}
impl<'ctx> CodeGenerator<'ctx> {
    fn new(context: &'ctx Context, program_name: &str) -> CodeGenerator<'ctx> {
        let module = context.create_module(program_name);
        let builder = context.create_builder();
        let string_type = context.struct_type(
            &[
                context.ptr_type(AddressSpace::default()).into(),
                context.i64_type().into(),
            ],
            false,
        );
        let concat_fn: FunctionValue<'_> = module.add_function(
            "oxide_string_concat",
            string_type.fn_type(&[string_type.into(), string_type.into()], false),
            None,
        );
        CodeGenerator {
            context,
            module,
            builder,
            functions: HashMap::new(),
            variables: vec![HashMap::new()],
            loop_stack: Vec::new(),
            string_type: string_type,
            string_concat_fn: concat_fn,
        }
    }

    fn push_scope(&mut self) {
        self.variables.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.variables.pop();
    }

    fn add_variable(&mut self, name: String, val: Variable<'ctx>) {
        self.variables
            .last_mut()
            .expect("ran out of scopes")
            .insert(name, val);
    }

    fn get_variable(&self, name: &String) -> &Variable<'ctx> {
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
            Type::Tuple(items) => todo!(),
            Type::Named { id, arguments } => todo!(),
            Type::GenericParameter(_) => todo!(),
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
                        self.context.i64_type().const_int(*n, false).into()
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
        let llvm_params = llvm_function.get_params();
        let entry = self.context.append_basic_block(*llvm_function, "entry");

        self.builder.position_at_end(entry);
        self.push_scope();
        for (param, value) in function.parameters.iter().zip(llvm_params) {
            let param_type = self.llvm_type(&param.param_type);
            let alloca = self
                .builder
                .build_alloca(param_type, &param.name)
                .expect("failed to build func param alloca");

            self.builder
                .build_store(alloca, value)
                .expect("failed to build func param store");
            let variable = Variable {
                ptr: alloca,
                ty: param_type,
            };
            self.add_variable(param.name.clone(), variable);
        }
        for statement in &body.statements {
            if self.current_block_has_terminator() {
                unreachable!("statements found after terminator");
            }
            self.compile_statement(statement)?;
        }

        if !self.current_block_has_terminator() {
            if function.signature.return_type == Type::Unit {
                self.builder
                    .build_return(None)
                    .expect("failed to built void return");
            } else {
                self.pop_scope();
                panic!("Missing return statement in non unit type function");
            }
        }
        let compiled_function = self
            .functions
            .get(&function.id)
            .expect(format!("function {} was not declared", function.signature.name).as_str());
        if !compiled_function.verify(true) {
            return Err(CompilerError::InvalidFunction);
        }
        self.pop_scope();
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
            Statement::Let { .. } => self.compile_let(statement, &function)?,
            Statement::Assignment { .. } => self.compile_assignment(statement)?,
            Statement::If { .. } => self.compile_if(statement, &function)?,
            Statement::While { .. } => self.compile_while(statement, &function)?,
            Statement::For { .. } => self.compile_for(statement, &function)?,
            Statement::Scope { .. } => self.compile_scope(statement)?,
            Statement::ExpressionStatement { expression } => match expression {
                Expression::ResolvedFunctionCall {
                    function_id,
                    arguments,
                } => {
                    self.compile_function_call(function_id, arguments)?;
                }
                _ => {
                    self.compile_expression(expression)?;
                }
            },
            Statement::Return { .. } => self.compile_return(statement)?,
            Statement::Break => {
                let loop_context = self.loop_stack.last_mut().expect("no loop context");
                self.builder
                    .build_unconditional_branch(loop_context.break_target)
                    .expect("failed to build unconditional branch to break target");
            }
            Statement::Continue => {
                let loop_context = self.loop_stack.last_mut().expect("no loop context");
                self.builder
                    .build_unconditional_branch(loop_context.continue_target)
                    .expect("failed to build unconditional branch to continue target");
            }
            Statement::FunctionDefinition { .. } => {
                unreachable!("Function definitions should be declared before compilation")
            }
            Statement::Pass => {
                unreachable!("Pass statements should be not be present in the checked program")
            }
        }
        Ok(())
    }

    fn compile_let(
        &mut self,
        statement: &Statement,
        function: &FunctionValue<'ctx>,
    ) -> Result<(), CompilerError> {
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
            &var_type
                .clone()
                .expect(format!("unknown type of variable {}", identifier).as_str()),
        );
        let initialiser = self.compile_expression(expression)?;
        let alloca = self.build_entry_alloca(function, llvm_type, identifier);
        self.builder
            .build_store(alloca, initialiser)
            .expect("failed to build store");
        let variable = Variable {
            ptr: alloca,
            ty: llvm_type,
        };
        self.add_variable(identifier.clone(), variable);

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

        let alloca = self.get_variable(identifier).ptr;
        let value = self.compile_expression(expression)?;
        self.builder
            .build_store(alloca, value)
            .expect("failed to build store");

        Ok(())
    }

    fn build_entry_alloca(
        &self,
        function: &FunctionValue<'ctx>,
        llvm_type: BasicTypeEnum<'ctx>,
        name: &str,
    ) -> PointerValue<'ctx> {
        let entry = function
            .get_first_basic_block()
            .expect("function has no entry block");

        let entry_builder = self.context.create_builder();

        if let Some(first_instruction) = entry.get_first_instruction() {
            entry_builder.position_before(&first_instruction);
        } else {
            entry_builder.position_at_end(entry);
        }

        entry_builder
            .build_alloca(llvm_type, name)
            .expect("failed to build alloca")
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

        let condition_value = self.compile_expression(condition)?;

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
        function: &FunctionValue<'ctx>,
    ) -> Result<(), CompilerError> {
        let Statement::While { condition, body } = statement else {
            return Err(CompilerError::WrongStatementType(
                "While".into(),
                format!("{:?}", statement),
            ));
        };

        let check_block = self.context.append_basic_block(*function, "check");
        let then_block = self.context.append_basic_block(*function, "then");
        let merge_block = self.context.append_basic_block(*function, "merge");

        self.loop_stack.push(LoopContext {
            break_target: merge_block,
            continue_target: check_block,
        });

        self.builder
            .build_unconditional_branch(check_block)
            .expect("failed to unconditionally branch to check block");

        self.builder.position_at_end(check_block);

        let condition_value = self.compile_expression(condition)?;

        self.builder
            .build_conditional_branch(condition_value.into_int_value(), then_block, merge_block)
            .expect("failed to build conditional branch");
        self.builder.position_at_end(then_block);
        for statement in body {
            if self.current_block_has_terminator() {
                unreachable!("statements found after terminator");
            }
            self.compile_statement(statement)?;
        }
        self.loop_stack.pop();
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
        function: &FunctionValue<'ctx>,
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
        let increment_block = self.context.append_basic_block(*function, "increment");
        let merge_block = self.context.append_basic_block(*function, "merge");

        self.loop_stack.push(LoopContext {
            break_target: merge_block,
            continue_target: increment_block,
        });

        self.builder
            .build_unconditional_branch(check_block)
            .expect("failed to unconditionally branch to check block");

        self.builder.position_at_end(check_block);
        if let Some(cond) = condition {
            let condition_res = self.compile_expression(cond)?;
            self.builder
                .build_conditional_branch(condition_res.into_int_value(), then_block, merge_block)
                .expect("failed to build conditional branch in for");
        } else {
            self.builder
                .build_unconditional_branch(then_block)
                .expect("failed to build unconditional branch in for");
        }
        self.builder.position_at_end(then_block);
        for statement in body {
            if self.current_block_has_terminator() {
                unreachable!("statements found after terminator");
            }
            self.compile_statement(statement)?;
        }
        if !self.current_block_has_terminator() {
            self.builder
                .build_unconditional_branch(increment_block)
                .expect("failed to build unconditional branch to increment block.");
        }

        self.builder.position_at_end(increment_block);

        if let Some(inc) = increment {
            self.compile_statement(inc)?;
        }

        if !self.current_block_has_terminator() {
            self.builder
                .build_unconditional_branch(check_block)
                .expect("failed to build unconditional branch to check block.");
        }

        self.loop_stack.pop();

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
            Some(self.compile_expression(val)?)
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
            Expression::Identifier(name) => self.compile_identifier(name),
            Expression::BinaryOp {
                left,
                operator,
                right,
                inferred_type,
            } => self.compile_binary_op(
                left,
                operator,
                right,
                &inferred_type
                    .clone()
                    .expect("no inferred type in binary op"),
            ),
            Expression::UnaryOp {
                operator,
                operand,
                inferred_type,
            } => self.compile_unary_op(
                operator,
                operand,
                &inferred_type.clone().expect("no inferred type in unary op"),
            ),
            Expression::ResolvedFunctionCall {
                function_id,
                arguments,
            } => self
                .compile_function_call(function_id, arguments)?
                .ok_or(CompilerError::InvalidFunction),
            Expression::UnresolvedFunctionCall { .. } => {
                unreachable!("unresolve function call reached compiler")
            }
        }
    }

    fn compile_identifier(&self, name: &String) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        let variable = self.get_variable(name);
        let temp_name = format!(
            "tmp_{}",
            variable
                .ptr
                .get_name()
                .to_str()
                .expect("invalid variable name")
        );
        let value = self
            .builder
            .build_load(variable.ty, variable.ptr, temp_name.as_str())
            .expect("failed to build load ident");
        Ok(value)
    }

    fn compile_binary_op(
        &mut self,
        left: &Expression,
        op: &TokenType,
        right: &Expression,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        let left_val = self.compile_expression(left)?;
        let right_val = self.compile_expression(right)?;
        match op {
            TokenType::Plus => self.compile_add(left_val, right_val, ty),
            TokenType::Minus => self.compile_sub(left_val, right_val, ty),
            TokenType::Asterisk => self.compile_mul(left_val, right_val, ty),
            TokenType::Slash => self.compile_div(left_val, right_val, ty),
            TokenType::Modulo => self.compile_mod(left_val, right_val, ty),
            TokenType::GreaterThan => self.compile_gt(left_val, right_val, ty),
            TokenType::LessThan => self.compile_lt(left_val, right_val, ty),
            TokenType::GreaterThanOrEqualTo => self.compile_gte(left_val, right_val, ty),
            TokenType::LessThanOrEqualTo => self.compile_lte(left_val, right_val, ty),
            TokenType::EqualTo => self.compile_eq(left_val, right_val, ty),
            TokenType::NotEqualTo => self.compile_neq(left_val, right_val, ty),
            TokenType::LogicalAnd => self.compile_and(left_val, right_val, ty),
            TokenType::LogicalOr => self.compile_or(left_val, right_val, ty),
            TokenType::Walrus => self.compile_walrus(left, right_val),
            _ => unreachable!("invalid binary operator during compilation"),
        }
    }

    fn compile_add(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64 => self.compile_int_add(left, right),
            Type::F32 | Type::F64 => self.compile_float_add(left, right),
            Type::String => self.compile_string_concat(left, right),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_int_add(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_add(left.into_int_value(), right.into_int_value(), "isum")
            .map_err(|_| CompilerError::ExpressionBuilderError("int add".into()))?
            .as_basic_value_enum())
    }

    fn compile_float_add(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_float_add(left.into_float_value(), right.into_float_value(), "fsum")
            .map_err(|_| CompilerError::ExpressionBuilderError("float add".into()))?
            .as_basic_value_enum())
    }

    fn compile_string_concat(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        let left = left.into_struct_value();
        let right = right.into_struct_value();
        let result = self
            .builder
            .build_call(
                self.string_concat_fn,
                &[left.into(), right.into()],
                "strsum",
            )
            .expect("failed to build string concat function call");
        Ok(result
            .try_as_basic_value()
            .basic()
            .expect("no basic value as concat result"))
    }

    fn compile_sub(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64 => self.compile_int_sub(left, right),
            Type::F32 | Type::F64 => self.compile_float_sub(left, right),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_int_sub(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_sub(left.into_int_value(), right.into_int_value(), "idiff")
            .map_err(|_| CompilerError::ExpressionBuilderError("int sub".into()))?
            .as_basic_value_enum())
    }

    fn compile_float_sub(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_float_sub(left.into_float_value(), right.into_float_value(), "fdiff")
            .map_err(|_| CompilerError::ExpressionBuilderError("float sub".into()))?
            .as_basic_value_enum())
    }

    fn compile_mul(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64 => self.compile_int_mul(left, right),
            Type::F32 | Type::F64 => self.compile_float_mul(left, right),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_int_mul(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_mul(left.into_int_value(), right.into_int_value(), "iprod")
            .map_err(|_| CompilerError::ExpressionBuilderError("int mul".into()))?
            .as_basic_value_enum())
    }

    fn compile_float_mul(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_float_mul(left.into_float_value(), right.into_float_value(), "fprod")
            .map_err(|_| CompilerError::ExpressionBuilderError("float mul".into()))?
            .as_basic_value_enum())
    }

    fn compile_div(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8 | Type::U16 | Type::U32 | Type::U64 => self.compile_uint_div(left, right),
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => self.compile_int_div(left, right),
            Type::F32 | Type::F64 => self.compile_float_div(left, right),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_uint_div(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_unsigned_div(left.into_int_value(), right.into_int_value(), "uquot")
            .map_err(|_| CompilerError::ExpressionBuilderError("uint div".into()))?
            .as_basic_value_enum())
    }

    fn compile_int_div(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_signed_div(left.into_int_value(), right.into_int_value(), "iquot")
            .map_err(|_| CompilerError::ExpressionBuilderError("int div".into()))?
            .as_basic_value_enum())
    }

    fn compile_float_div(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_float_div(left.into_float_value(), right.into_float_value(), "fquot")
            .map_err(|_| CompilerError::ExpressionBuilderError("float div".into()))?
            .as_basic_value_enum())
    }

    fn compile_mod(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8 | Type::U16 | Type::U32 | Type::U64 => self.compile_uint_mod(left, right),
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => self.compile_int_mod(left, right),
            Type::F32 | Type::F64 => self.compile_float_mod(left, right),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_uint_mod(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_unsigned_rem(left.into_int_value(), right.into_int_value(), "umod")
            .map_err(|_| CompilerError::ExpressionBuilderError("uint mod".into()))?
            .as_basic_value_enum())
    }

    fn compile_int_mod(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_signed_rem(left.into_int_value(), right.into_int_value(), "imod")
            .map_err(|_| CompilerError::ExpressionBuilderError("int mod".into()))?
            .as_basic_value_enum())
    }

    fn compile_float_mod(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_float_rem(left.into_float_value(), right.into_float_value(), "fmod")
            .map_err(|_| CompilerError::ExpressionBuilderError("float mod".into()))?
            .as_basic_value_enum())
    }

    fn compile_gt(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8 | Type::U16 | Type::U32 | Type::U64 => self.compile_uint_gt(left, right),
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => self.compile_int_gt(left, right),
            Type::F32 | Type::F64 => self.compile_float_gt(left, right),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_uint_gt(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_compare(
                IntPredicate::UGT,
                left.into_int_value(),
                right.into_int_value(),
                "ugt",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("uint gt".into()))?
            .as_basic_value_enum())
    }

    fn compile_int_gt(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_compare(
                IntPredicate::SGT,
                left.into_int_value(),
                right.into_int_value(),
                "igt",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("int gt".into()))?
            .as_basic_value_enum())
    }

    fn compile_float_gt(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_float_compare(
                FloatPredicate::OGT,
                left.into_float_value(),
                right.into_float_value(),
                "fgt",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("float gt".into()))?
            .as_basic_value_enum())
    }

    fn compile_gte(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8 | Type::U16 | Type::U32 | Type::U64 => self.compile_uint_gte(left, right),
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => self.compile_int_gte(left, right),
            Type::F32 | Type::F64 => self.compile_float_gte(left, right),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_uint_gte(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_compare(
                IntPredicate::UGE,
                left.into_int_value(),
                right.into_int_value(),
                "ugte",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("uint gte".into()))?
            .as_basic_value_enum())
    }

    fn compile_int_gte(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_compare(
                IntPredicate::SGE,
                left.into_int_value(),
                right.into_int_value(),
                "igte",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("int gte".into()))?
            .as_basic_value_enum())
    }

    fn compile_float_gte(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_float_compare(
                FloatPredicate::OGE,
                left.into_float_value(),
                right.into_float_value(),
                "fgte",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("float gte".into()))?
            .as_basic_value_enum())
    }

    fn compile_lt(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8 | Type::U16 | Type::U32 | Type::U64 => self.compile_uint_lt(left, right),
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => self.compile_int_lt(left, right),
            Type::F32 | Type::F64 => self.compile_float_lt(left, right),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_uint_lt(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_compare(
                IntPredicate::ULT,
                left.into_int_value(),
                right.into_int_value(),
                "ult",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("uint lt".into()))?
            .as_basic_value_enum())
    }

    fn compile_int_lt(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_compare(
                IntPredicate::SLT,
                left.into_int_value(),
                right.into_int_value(),
                "ilt",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("int lt".into()))?
            .as_basic_value_enum())
    }

    fn compile_float_lt(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_float_compare(
                FloatPredicate::OLT,
                left.into_float_value(),
                right.into_float_value(),
                "flt",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("float lt".into()))?
            .as_basic_value_enum())
    }

    fn compile_lte(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8 | Type::U16 | Type::U32 | Type::U64 => self.compile_uint_lte(left, right),
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => self.compile_int_lte(left, right),
            Type::F32 | Type::F64 => self.compile_float_lte(left, right),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_uint_lte(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_compare(
                IntPredicate::ULE,
                left.into_int_value(),
                right.into_int_value(),
                "ulte",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("uint lte".into()))?
            .as_basic_value_enum())
    }

    fn compile_int_lte(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_compare(
                IntPredicate::SLE,
                left.into_int_value(),
                right.into_int_value(),
                "ilte",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("int lte".into()))?
            .as_basic_value_enum())
    }

    fn compile_float_lte(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_float_compare(
                FloatPredicate::OLE,
                left.into_float_value(),
                right.into_float_value(),
                "flte",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("float lte".into()))?
            .as_basic_value_enum())
    }

    fn compile_eq(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64 => self.compile_int_eq(left, right),
            Type::F32 | Type::F64 => self.compile_float_eq(left, right),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_int_eq(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_compare(
                IntPredicate::EQ,
                left.into_int_value(),
                right.into_int_value(),
                "ieq",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("int eq".into()))?
            .as_basic_value_enum())
    }

    fn compile_float_eq(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_float_compare(
                FloatPredicate::OEQ,
                left.into_float_value(),
                right.into_float_value(),
                "feq",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("float eq".into()))?
            .as_basic_value_enum())
    }

    fn compile_neq(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64 => self.compile_int_neq(left, right),
            Type::F32 | Type::F64 => self.compile_float_neq(left, right),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_int_neq(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_compare(
                IntPredicate::NE,
                left.into_int_value(),
                right.into_int_value(),
                "ineq",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("int neq".into()))?
            .as_basic_value_enum())
    }

    fn compile_float_neq(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_float_compare(
                FloatPredicate::ONE,
                left.into_float_value(),
                right.into_float_value(),
                "fneq",
            )
            .map_err(|_| CompilerError::ExpressionBuilderError("float neq".into()))?
            .as_basic_value_enum())
    }

    fn compile_and(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        if !matches!(ty, Type::Bool) {
            unreachable!("invalid type during compilation");
        }

        let left = left.into_int_value();
        let right = right.into_int_value();
        Ok(self
            .builder
            .build_and(left, right, "and")
            .map_err(|_| CompilerError::ExpressionBuilderError("and".into()))?
            .as_basic_value_enum())
    }

    fn compile_or(
        &self,
        left: BasicValueEnum<'ctx>,
        right: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        if !matches!(ty, Type::Bool) {
            unreachable!("invalid type during compilation");
        }

        let left = left.into_int_value();
        let right = right.into_int_value();
        Ok(self
            .builder
            .build_or(left, right, "or")
            .map_err(|_| CompilerError::ExpressionBuilderError("or".into()))?
            .as_basic_value_enum())
    }

    fn compile_walrus(
        &self,
        left: &Expression,
        right: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        let Expression::Identifier(ident) = left else {
            unreachable!("non-ident increment reached compiler");
        };
        let var_ptr = self.get_variable(ident).ptr;
        self.builder
            .build_store(var_ptr, right)
            .expect("failed to build store");
        Ok(right)
    }

    fn compile_unary_op(
        &mut self,
        operator: &TokenType,
        operand: &Expression,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match operator {
            TokenType::Increment => self.compile_inc(operand, ty),
            TokenType::Decrement => self.compile_dec(operand, ty),
            TokenType::Minus => {
                let operand = self.compile_expression(operand)?;
                self.compile_neg(operand, ty)
            }
            TokenType::Not => {
                let operand = self.compile_expression(operand)?;
                self.compile_not(operand, ty)
            }
            _ => unreachable!("invalid binary operator during compilation"),
        }
    }

    fn compile_inc(
        &mut self,
        operand: &Expression,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64 => self.compile_int_inc(operand, ty),
            Type::F32 | Type::F64 => self.compile_float_inc(operand, ty),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_int_inc(
        &mut self,
        operand: &Expression,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        let Expression::Identifier(ident) = operand else {
            unreachable!("non-ident increment reached compiler");
        };
        let one_int = self.llvm_type(ty).into_int_type().const_int(1, false);
        let operand_value = self.compile_expression(operand)?;
        let result = self
            .builder
            .build_int_add(operand_value.into_int_value(), one_int, "iinc")
            .map_err(|_| CompilerError::ExpressionBuilderError("int inc".into()))?
            .as_basic_value_enum();

        let var_ptr = self.get_variable(ident).ptr;
        self.builder
            .build_store(var_ptr, result)
            .expect("failed to build store");
        Ok(result)
    }

    fn compile_float_inc(
        &mut self,
        operand: &Expression,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        let Expression::Identifier(ident) = operand else {
            unreachable!("non-ident increment reached compiler");
        };
        let one_float = self.llvm_type(ty).into_float_type().const_float(1.0);
        let operand_value = self.compile_expression(operand)?;
        let result = self
            .builder
            .build_float_add(operand_value.into_float_value(), one_float, "finc")
            .map_err(|_| CompilerError::ExpressionBuilderError("float inc".into()))?
            .as_basic_value_enum();

        let var_ptr = self.get_variable(ident).ptr;
        self.builder
            .build_store(var_ptr, result)
            .expect("failed to build store");
        Ok(result)
    }

    fn compile_dec(
        &mut self,
        operand: &Expression,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64 => self.compile_int_dec(operand, ty),
            Type::F32 | Type::F64 => self.compile_float_dec(operand, ty),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_int_dec(
        &mut self,
        operand: &Expression,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        let Expression::Identifier(ident) = operand else {
            unreachable!("non-ident decrement reached compiler");
        };
        let one_int = self.llvm_type(ty).into_int_type().const_int(1, false);
        let operand_value = self.compile_expression(operand)?;
        let result = self
            .builder
            .build_int_sub(operand_value.into_int_value(), one_int, "idec")
            .map_err(|_| CompilerError::ExpressionBuilderError("int dec".into()))?
            .as_basic_value_enum();

        let var_ptr = self.get_variable(ident).ptr;
        self.builder
            .build_store(var_ptr, result)
            .expect("failed to build store");
        Ok(result)
    }

    fn compile_float_dec(
        &mut self,
        operand: &Expression,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        let Expression::Identifier(ident) = operand else {
            unreachable!("non-ident decrement reached compiler");
        };
        let one_float = self.llvm_type(ty).into_float_type().const_float(1.0);
        let operand_value = self.compile_expression(operand)?;
        let result = self
            .builder
            .build_float_sub(operand_value.into_float_value(), one_float, "fdec")
            .map_err(|_| CompilerError::ExpressionBuilderError("float dec".into()))?
            .as_basic_value_enum();

        let var_ptr = self.get_variable(ident).ptr;
        self.builder
            .build_store(var_ptr, result)
            .expect("failed to build store");
        Ok(result)
    }

    fn compile_neg(
        &self,
        operand: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            Type::U8 | Type::U16 | Type::U32 | Type::U64 => {
                unreachable!("invalid type during compilation")
            }
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => self.compile_int_neg(operand),
            Type::F32 | Type::F64 => self.compile_float_neg(operand),
            _ => unreachable!("invalid type during compilation"),
        }
    }

    fn compile_int_neg(
        &self,
        operand: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_int_neg(operand.into_int_value(), "ineg")
            .map_err(|_| CompilerError::ExpressionBuilderError("int neg".into()))?
            .as_basic_value_enum())
    }

    fn compile_float_neg(
        &self,
        operand: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        Ok(self
            .builder
            .build_float_neg(operand.into_float_value(), "fneg")
            .map_err(|_| CompilerError::ExpressionBuilderError("float neg".into()))?
            .as_basic_value_enum())
    }

    fn compile_not(
        &self,
        operand: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        if !matches!(ty, Type::Bool) {
            unreachable!("invalid type during compilation");
        }
        Ok(self
            .builder
            .build_not(operand.into_int_value(), "not")
            .map_err(|_| CompilerError::ExpressionBuilderError("not".into()))?
            .as_basic_value_enum())
    }

    fn compile_function_call(
        &mut self,
        function_id: &FunctionId,
        arguments: &Vec<Expression>,
    ) -> Result<Option<BasicValueEnum<'ctx>>, CompilerError> {
        let func = *self
            .functions
            .get(function_id)
            .expect("failed to get function");

        let values: Vec<BasicValueEnum<'ctx>> = arguments
            .iter()
            .map(|argument| self.compile_expression(argument))
            .collect::<Result<_, _>>()?;

        let args: Vec<BasicMetadataValueEnum<'ctx>> = values.into_iter().map(Into::into).collect();
        let result_name = format!(
            "call_{}_res",
            func.get_name().to_str().expect("invalid function name")
        );
        let call = self
            .builder
            .build_call(func, &args, result_name.as_str())
            .expect("failed to build function call");

        Ok(call.try_as_basic_value().basic())
    }
}

#[derive(Debug)]
enum CompilerError {
    ExpressionBuilderError(String),
    WrongStatementType(String, String),
    InvalidFunction,
    CouldNotReadFile(String),
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        println!("Please provide a file to compile, and the name of the object file to produce.");
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

    declare_global_variables(&mut code_gen, &program);

    match compile_all_functions(&mut code_gen, &program) {
        Ok(_) => {}
        Err(err) => {
            match err {
                CompilerError::WrongStatementType(expected, got) => {
                    println!("Incorrect statement. Expected {expected}, got {got}");
                }
                CompilerError::InvalidFunction => println!("Function invalid."),
                CompilerError::CouldNotReadFile(_) => {
                    unreachable!("unexpected error when compiling all functions");
                }
                CompilerError::ExpressionBuilderError(msg) => {
                    println!("Expression builder error: {}", msg)
                }
            }
            std::process::exit(1);
        }
    }

    let oxide_main = program
        .function_table
        .get(&program.main_function_id)
        .unwrap();
    generate_main_function(&mut code_gen, &oxide_main);
    produce_object_file(&code_gen.module, &args[2]);
}

fn get_program_from_file(file_path: &str) -> Result<CheckedProgram, CompilerError> {
    let ast = std::fs::read_to_string(&file_path)
        .map_err(|e| CompilerError::CouldNotReadFile(e.to_string()))?;
    let program: CheckedProgram =
        serde_json::from_str(&ast).map_err(|e| CompilerError::CouldNotReadFile(e.to_string()))?;
    Ok(program)
}

fn declare_global_variables(code_gen: &mut CodeGenerator, program: &CheckedProgram) {
    for variable in &program.globals {
        match variable {
            Statement::Let {
                identifier,
                expression,
                mutable: _,
                var_type,
            } => {
                let llvm_type =
                    code_gen.llvm_type(&var_type.clone().expect(
                        format!("unknown type of global variable {}", identifier).as_str(),
                    ));
                let initialiser = code_gen.const_expression(expression);
                let global_variable = code_gen.module.add_global(llvm_type, None, &identifier);
                global_variable.set_initializer(&initialiser);
                let variable = Variable {
                    ptr: global_variable.as_pointer_value(),
                    ty: llvm_type,
                };
                code_gen.add_variable(identifier.clone(), variable);
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
        let function_name = get_function_name(&function);
        let function_value = code_gen
            .module
            .add_function(&function_name, function_type, None);
        code_gen
            .functions
            .insert(function.id.clone(), function_value);
    }
}

fn compile_all_functions(
    code_gen: &mut CodeGenerator,
    program: &CheckedProgram,
) -> Result<(), CompilerError> {
    for function in &program.function_table.functions {
        // only compile user defined functions, builtins will be linked later
        if matches!(function.implementation, FunctionImplementation::Oxide(_)) {
            code_gen.compile_function(function)?;
        }
    }
    Ok(())
}

fn generate_main_function(code_gen: &mut CodeGenerator, oxide_main: &Function) {
    let oxide_main = code_gen
        .functions
        .get(&oxide_main.id)
        .expect(format!("function {} was not declared", oxide_main.signature.name).as_str());
    let main_type = code_gen.context.i32_type().fn_type(&[], false);
    let llvm_main = code_gen.module.add_function("main", main_type, None);
    let entry = code_gen.context.append_basic_block(llvm_main, "entry");
    code_gen.builder.position_at_end(entry);
    code_gen
        .builder
        .build_call(*oxide_main, &[], "call_oxide_main")
        .expect("failed to build call to oxide main");
    let int_zero = code_gen.context.i32_type().const_zero();
    code_gen
        .builder
        .build_return(Some(&int_zero))
        .expect("failed to build return");
}

#[allow(dead_code)]
fn print_ir(code_gen: &CodeGenerator) {
    // for debugging
    println!("{}", code_gen.module.print_to_string().to_string());
}

fn produce_object_file(module: &Module, file_path: &str) {
    Target::initialize_aarch64(&InitializationConfig::default());
    let triple = TargetMachine::get_default_triple();
    let target = Target::from_triple(&triple).expect("uhh");
    let target_machine = target
        .create_target_machine(
            &triple,
            "generic",
            "",
            OptimizationLevel::Aggressive,
            RelocMode::Default,
            CodeModel::Default,
        )
        .expect("uhh");
    target_machine
        .write_to_file(&module, FileType::Object, Path::new(file_path))
        .expect("failed to write to object file");
}

fn get_function_name(function: &Function) -> String {
    match &function.implementation {
        FunctionImplementation::Oxide(_) => {
            return format!("{}_{}", function.signature.name, function.id.0);
        }
        FunctionImplementation::Builtin(_) => {
            let mut name = String::from("oxide_");
            name.push_str(&function.signature.name);
            name.push_str("_");
            for param in &function.parameters {
                name.push_str(&param.param_type.to_string());
                name.push_str("_");
            }
            name.push_str(&function.signature.return_type.to_string());
            name
        }
    }
}
