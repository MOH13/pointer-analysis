use either::Either;
use llvm_ir::function::ParameterAttribute;
use llvm_ir::instruction::{
    AddrSpaceCast, Alloca, BitCast, Call, InlineAssembly, Load, Phi, Store,
};
use llvm_ir::terminator::{Invoke, Ret};
use llvm_ir::{
    BasicBlock, Constant, Function, Instruction, Module, Name, Operand, Terminator, Type, TypeRef,
};

#[derive(Clone, Copy)]
pub struct Context<'a> {
    pub module: &'a Module,
    pub function: &'a Function,
    pub block: &'a BasicBlock,
}

/// This trait allows implementors to define the `handle_instruction` and `handle_terminator` functions,
/// which the `visit_module` function will call on all instructions and terminators.
pub trait ModuleVisitor<'a> {
    fn handle_function(&mut self, function: &'a Function, module: &'a Module);
    fn handle_instruction(&mut self, instr: &'a Instruction, context: Context<'a>);
    fn handle_terminator(&mut self, term: &'a Terminator, context: Context<'a>);

    fn visit_module(&mut self, module: &'a Module) {
        for function in &module.functions {
            self.handle_function(function, module);
            for block in &function.basic_blocks {
                let context = Context {
                    module,
                    function,
                    block,
                };

                for instr in &block.instrs {
                    self.handle_instruction(instr, context);
                }
                self.handle_terminator(&block.term, context)
            }
        }
    }
}

pub enum PointerInstruction<'a> {
    /// x = y
    Assign { dest: &'a Name, value: &'a Name },
    /// *x = y
    Store { address: &'a Name, value: &'a Name },
    /// x = *y
    Load { dest: &'a Name, address: &'a Name },
    /// x = alloca ..
    Alloca { dest: &'a Name },
    /// x = \phi(y1, y2, ..)
    Phi {
        dest: &'a Name,
        incoming_values: Vec<&'a Name>,
    },
    /// [x =] f(y1, y2, ..)
    Call {
        dest: Option<&'a Name>,
        function: &'a str,
        arguments: Vec<Option<&'a Name>>,
    },
    /// return x
    Return { return_reg: &'a Name },
}

pub struct PointerContext<'a> {
    pub fun_name: &'a str,
}

pub trait PointerModuleVisitor<'a> {
    fn handle_ptr_function(&mut self, name: &'a str, parameters: Vec<&'a Name>);
    fn handle_ptr_instruction(
        &mut self,
        instr: PointerInstruction<'a>,
        context: PointerContext<'a>,
    );

    fn handle_call(
        &mut self,
        function: &'a Either<InlineAssembly, Operand>,
        arguments: &'a [(Operand, Vec<ParameterAttribute>)],
        dest: Option<&'a Name>,
        caller: &'a str,
    ) {
        // TODO: Filter out irrelevant function calls
        let (function, ty) = match function {
            Either::Right(Operand::ConstantOperand(name_ref)) => match name_ref.as_ref() {
                Constant::GlobalReference {
                    name: Name::Name(name),
                    ty,
                } => (&**name, ty),
                _ => return,
            },
            _ => return,
        };

        let dest = match ty.as_ref() {
            Type::FuncType { result_type, .. } if is_ptr_type(result_type) => dest,
            _ => None,
        };

        let arguments = arguments
            .iter()
            .map(|(arg, _)| get_operand_name_type(arg).map(|(name, _)| name))
            .collect();

        let instr = PointerInstruction::Call {
            dest,
            function,
            arguments,
        };
        let context = PointerContext { fun_name: caller };
        self.handle_ptr_instruction(instr, context);
    }
}

impl<'a, T: PointerModuleVisitor<'a>> ModuleVisitor<'a> for T {
    fn handle_function(&mut self, function: &'a Function, _module: &'a Module) {
        let parameters = function.parameters.iter().map(|p| &p.name).collect();
        self.handle_ptr_function(&function.name, parameters)
    }

    fn handle_instruction(
        &mut self,
        instr: &'a Instruction,
        Context { function, .. }: Context<'a>,
    ) {
        match instr {
            // Instruction::ExtractElement(_) => todo!(),
            // Instruction::ExtractValue(_) => todo!(),
            Instruction::Alloca(Alloca { dest, .. }) => {
                let instr = PointerInstruction::Alloca { dest };
                let context = PointerContext {
                    fun_name: &function.name,
                };
                self.handle_ptr_instruction(instr, context);
            }

            Instruction::BitCast(BitCast {
                operand,
                to_type,
                dest,
                ..
            })
            | Instruction::AddrSpaceCast(AddrSpaceCast {
                operand,
                to_type,
                dest,
                ..
            }) if is_ptr_type(to_type) => {
                if let Some((value, _)) = get_operand_name_type(operand) {
                    let instr = PointerInstruction::Assign { dest, value };
                    let context = PointerContext {
                        fun_name: &function.name,
                    };
                    self.handle_ptr_instruction(instr, context);
                };
            }

            // Instruction::GetElementPtr(_) => todo!(),
            // Instruction::IntToPtr(_) => todo!(),
            Instruction::Phi(Phi {
                incoming_values,
                dest,
                to_type,
                ..
            }) if is_ptr_type(to_type) => {
                let incoming_values = incoming_values
                    .iter()
                    .filter_map(|(value, _)| get_operand_name_type(value))
                    .map(|(name, _)| name)
                    .collect();

                let instr = PointerInstruction::Phi {
                    dest,
                    incoming_values,
                };
                let context = PointerContext {
                    fun_name: &function.name,
                };
                self.handle_ptr_instruction(instr, context);
            }

            Instruction::Load(Load { address, dest, .. }) => match get_operand_name_type(address) {
                Some((address, address_ty)) if is_ptr_ptr_type(address_ty) => {
                    let instr = PointerInstruction::Load { dest, address };
                    let context = PointerContext {
                        fun_name: &function.name,
                    };
                    self.handle_ptr_instruction(instr, context);
                }
                _ => {}
            },

            // *x = y
            Instruction::Store(Store { address, value, .. }) => {
                let value = match get_operand_name_type(value) {
                    Some((name, ty)) if is_ptr_type(ty) => name,
                    _ => return,
                };
                if let Some((address, _)) = get_operand_name_type(address) {
                    let instr = PointerInstruction::Store { address, value };
                    let context = PointerContext {
                        fun_name: &function.name,
                    };
                    self.handle_ptr_instruction(instr, context);
                }
            }

            // Instruction::Select(_) => todo!(),
            // Instruction::Freeze(_) => todo!(),
            Instruction::Call(Call {
                function: callee,
                arguments,
                dest,
                ..
            }) => self.handle_call(callee, arguments, dest.as_ref(), &function.name),

            // Instruction::VAArg(_) => todo!(),
            _ => {}
        }
    }

    fn handle_terminator(
        &mut self,
        term: &'a Terminator,
        Context {
            function: context_fun,
            ..
        }: Context<'a>,
    ) {
        match term {
            Terminator::Invoke(Invoke {
                function,
                arguments,
                result,
                ..
            }) => self.handle_call(function, arguments, Some(result), &context_fun.name),

            Terminator::Ret(Ret { return_operand, .. }) => {
                let return_reg = match return_operand.as_ref().and_then(get_operand_name_type) {
                    Some((name, ty)) if is_ptr_type(ty) => name,
                    _ => return,
                };

                let instr = PointerInstruction::Return { return_reg };
                let context = PointerContext {
                    fun_name: &context_fun.name,
                };
                self.handle_ptr_instruction(instr, context);
            }

            _ => {}
        }
    }
}

fn is_ptr_type(ty: &TypeRef) -> bool {
    matches!(ty.as_ref(), Type::PointerType { .. })
}

fn is_ptr_ptr_type(ty: &TypeRef) -> bool {
    match ty.as_ref() {
        Type::PointerType { pointee_type, .. } => is_ptr_type(pointee_type),
        _ => false,
    }
}

fn get_operand_name_type(operand: &Operand) -> Option<(&Name, &TypeRef)> {
    match operand {
        Operand::LocalOperand { name, ty } => Some((name, ty)),
        Operand::ConstantOperand(constant) => match constant.as_ref() {
            llvm_ir::Constant::GlobalReference { name, ty } => Some((name, ty)),
            _ => None,
        },
        Operand::MetadataOperand => None,
    }
}
