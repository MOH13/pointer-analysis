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

enum PointerInstruction<'a> {
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
    /// (x =) f(y_1, y_2, ..)
    Call {
        dest: Option<&'a Name>,
        function: &'a str,
        arguments: Vec<Option<&'a Name>>,
    },
}

struct PointerContext;

pub trait PointerVisitor {
    fn handle_ptr_instruction(&mut self, instr: PointerInstruction, context: PointerContext);

    fn handle_call(
        &mut self,
        function: &Either<InlineAssembly, Operand>,
        arguments: &[(Operand, Vec<ParameterAttribute>)],
        dest: Option<&Name>,
        context: Context,
    ) {
        let function = match function {
            Either::Right(Operand::ConstantOperand(name_ref)) => match name_ref.as_ref() {
                Constant::GlobalReference {
                    name: Name::Name(name),
                    ..
                } => &**name,
                _ => return,
            },
            _ => return,
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
        self.handle_ptr_instruction(instr, PointerContext)
    }
}

impl<T: PointerVisitor> ModuleVisitor for T {
    fn handle_function(&mut self, function: &Function, module: &Module) {
        todo!()
    }

    fn handle_instruction(&mut self, instr: &Instruction, context: Context) {
        match instr {
            Instruction::Alloca(Alloca { dest, .. }) => {
                let instr = PointerInstruction::Alloca { dest };
                self.handle_ptr_instruction(instr, PointerContext);
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
            }) if is_pointer_type(to_type) => {
                if let Some((value, _)) = get_operand_name_type(operand) {
                    let instr = PointerInstruction::Assign { dest, value };
                    self.handle_ptr_instruction(instr, PointerContext);
                };
            }

            Instruction::Phi(Phi {
                incoming_values,
                dest,
                to_type,
                ..
            }) if is_pointer_type(to_type) => {
                let incoming_values = incoming_values
                    .iter()
                    .filter_map(|(value, _)| get_operand_name_type(value))
                    .map(|(name, _)| name)
                    .collect();

                let instr = PointerInstruction::Phi {
                    dest,
                    incoming_values,
                };
                self.handle_ptr_instruction(instr, PointerContext);
            }

            Instruction::Load(Load { address, dest, .. }) => match get_operand_name_type(address) {
                Some((address, address_ty)) if is_pointer_pointer_type(address_ty) => {
                    let instr = PointerInstruction::Load { dest, address };
                    self.handle_ptr_instruction(instr, PointerContext);
                }
                _ => {}
            },

            // *x = y
            Instruction::Store(Store { address, value, .. }) => {
                let value = match get_operand_name_type(value) {
                    Some((name, ty)) if is_pointer_type(ty) => name,
                    _ => return,
                };
                if let Some((address, _)) = get_operand_name_type(address) {
                    let instr = PointerInstruction::Store { address, value };
                    self.handle_ptr_instruction(instr, PointerContext);
                }
            }

            Instruction::Call(Call {
                function,
                arguments,
                dest,
                ..
            }) => self.handle_call(function, arguments, dest.as_ref(), context),

            _ => {}
        }
    }

    fn handle_terminator(&mut self, term: &Terminator, context: Context) {
        match term {
            Terminator::Invoke(Invoke {
                function,
                arguments,
                result,
                ..
            }) => self.handle_call(function, arguments, Some(result), context),

            _ => {}
        }
    }
}

fn is_pointer_type(ty: &TypeRef) -> bool {
    matches!(ty.as_ref(), Type::PointerType { .. })
}

fn is_pointer_pointer_type(ty: &TypeRef) -> bool {
    match ty.as_ref() {
        Type::PointerType { pointee_type, .. } => is_pointer_type(pointee_type),
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
