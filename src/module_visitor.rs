use either::Either;
use llvm_ir::function::ParameterAttribute;
use llvm_ir::instruction::{
    AddrSpaceCast, Alloca, BitCast, Call, InlineAssembly, Load, Phi, Store,
};
use llvm_ir::terminator::Invoke;
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
pub trait ModuleVisitor {
    fn handle_function(&mut self, function: &Function, module: &Module);
    fn handle_instruction(&mut self, instr: &Instruction, context: Context);
    fn handle_terminator(&mut self, term: &Terminator, context: Context);

    fn visit_module(&mut self, module: &Module) {
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
}

pub struct PointerContext<'a> {
    function: &'a str,
}

pub trait PointerVisitor {
    fn handle_ptr_function(&mut self, name: &str, parameters: Vec<&Name>);
    fn handle_ptr_instruction(&mut self, instr: PointerInstruction, context: PointerContext);

    fn handle_call(
        &mut self,
        function: &Either<InlineAssembly, Operand>,
        arguments: &[(Operand, Vec<ParameterAttribute>)],
        dest: Option<&Name>,
        caller: &str,
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
        let context = PointerContext { function: caller };
        self.handle_ptr_instruction(instr, context);
    }
}

impl<T: PointerVisitor> ModuleVisitor for T {
    fn handle_function(&mut self, function: &Function, _module: &Module) {
        let parameters = function.parameters.iter().map(|p| &p.name).collect();
        self.handle_ptr_function(&function.name, parameters)
    }

    fn handle_instruction(&mut self, instr: &Instruction, Context { function, .. }: Context) {
        match instr {
            Instruction::Alloca(Alloca { dest, .. }) => {
                let instr = PointerInstruction::Alloca { dest };
                let context = PointerContext {
                    function: &function.name,
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
                        function: &function.name,
                    };
                    self.handle_ptr_instruction(instr, context);
                };
            }

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
                    function: &function.name,
                };
                self.handle_ptr_instruction(instr, context);
            }

            Instruction::Load(Load { address, dest, .. }) => match get_operand_name_type(address) {
                Some((address, address_ty)) if is_ptr_ptr_type(address_ty) => {
                    let instr = PointerInstruction::Load { dest, address };
                    let context = PointerContext {
                        function: &function.name,
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
                        function: &function.name,
                    };
                    self.handle_ptr_instruction(instr, context);
                }
            }

            Instruction::Call(Call {
                function: callee,
                arguments,
                dest,
                ..
            }) => self.handle_call(callee, arguments, dest.as_ref(), &function.name),

            _ => {}
        }
    }

    fn handle_terminator(
        &mut self,
        term: &Terminator,
        Context {
            function: caller, ..
        }: Context,
    ) {
        match term {
            Terminator::Invoke(Invoke {
                function,
                arguments,
                result,
                ..
            }) => self.handle_call(function, arguments, Some(result), &caller.name),

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
