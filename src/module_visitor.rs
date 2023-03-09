use std::fmt::{self, Display, Formatter};

use either::Either;
use llvm_ir::function::ParameterAttribute;
use llvm_ir::instruction::{
    AddrSpaceCast, Alloca, BitCast, Call, InlineAssembly, Load, Phi, Store,
};
use llvm_ir::module::GlobalVariable;
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
    fn handle_global(&mut self, global: &'a GlobalVariable, module: &'a Module);
    fn handle_instruction(&mut self, instr: &'a Instruction, context: Context<'a>);
    fn handle_terminator(&mut self, term: &'a Terminator, context: Context<'a>);

    fn visit_module(&mut self, module: &'a Module) {
        for global in &module.global_vars {
            self.handle_global(global, module);
        }

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

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum VarIdent<'a> {
    Local {
        reg_name: &'a Name,
        fun_name: &'a str,
    },
    Global {
        name: &'a Name,
    },
}

impl<'a> VarIdent<'a> {
    fn new_local(reg_name: &'a Name, function: &'a Function) -> Self {
        Self::Local {
            reg_name,
            fun_name: &function.name,
        }
    }
}

impl<'a> Display for VarIdent<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            VarIdent::Local { reg_name, fun_name } => write!(f, "{reg_name}@{fun_name}"),
            VarIdent::Global { name } => write!(f, "{name}"),
        }
    }
}

pub enum PointerInstruction<'a> {
    /// x = y
    Assign {
        dest: VarIdent<'a>,
        value: VarIdent<'a>,
    },
    /// *x = y
    Store {
        address: VarIdent<'a>,
        value: VarIdent<'a>,
    },
    /// x = *y
    Load {
        dest: VarIdent<'a>,
        address: VarIdent<'a>,
    },
    /// x = alloca ..
    Alloca { dest: VarIdent<'a> },
    /// x = \phi(y1, y2, ..)
    Phi {
        dest: VarIdent<'a>,
        incoming_values: Vec<VarIdent<'a>>,
    },
    /// [x =] f(y1, y2, ..)
    Call {
        dest: Option<VarIdent<'a>>,
        function: &'a str,
        arguments: Vec<Option<VarIdent<'a>>>,
    },
    /// return x
    Return { return_reg: VarIdent<'a> },
}

pub trait PointerModuleVisitor<'a> {
    fn handle_ptr_function(&mut self, name: &'a str, parameters: Vec<VarIdent<'a>>);
    fn handle_ptr_global(&mut self, ident: VarIdent<'a>, init_ref: Option<VarIdent<'a>>);
    fn handle_ptr_instruction(&mut self, instr: PointerInstruction<'a>, fun_name: &'a str);

    fn handle_call(
        &mut self,
        function: &'a Either<InlineAssembly, Operand>,
        arguments: &'a [(Operand, Vec<ParameterAttribute>)],
        dest: Option<&'a Name>,
        Context {
            function: caller, ..
        }: Context<'a>,
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
            Type::FuncType { result_type, .. } if is_ptr_type(result_type) => {
                dest.map(|d| VarIdent::new_local(d, caller))
            }
            _ => None,
        };

        let arguments = arguments
            .iter()
            .map(|(arg, _)| get_operand_ident_type(arg, caller).map(|(ident, _)| ident))
            .collect();

        let instr = PointerInstruction::Call {
            dest,
            function,
            arguments,
        };
        self.handle_ptr_instruction(instr, &caller.name);
    }
}

impl<'a, T: PointerModuleVisitor<'a>> ModuleVisitor<'a> for T {
    fn handle_function(&mut self, function: &'a Function, _module: &'a Module) {
        let parameters = function
            .parameters
            .iter()
            .map(|p| VarIdent::new_local(&p.name, function))
            .collect();
        self.handle_ptr_function(&function.name, parameters)
    }

    fn handle_global(&mut self, global: &'a GlobalVariable, _module: &'a Module) {
        if !global.is_constant {
            let init_ref = global
                .initializer
                .as_ref()
                .and_then(|init| match init.as_ref() {
                    Constant::GlobalReference { name, .. } => Some(VarIdent::Global { name }),
                    _ => None,
                });
            self.handle_ptr_global(VarIdent::Global { name: &global.name }, init_ref);
        }
    }

    fn handle_instruction(
        &mut self,
        instr: &'a Instruction,
        context @ Context { function, .. }: Context<'a>,
    ) {
        match instr {
            // Instruction::ExtractElement(_) => todo!(),
            // Instruction::ExtractValue(_) => todo!(),
            Instruction::Alloca(Alloca { dest, .. }) => {
                let dest = VarIdent::new_local(dest, function);
                let instr = PointerInstruction::Alloca { dest };
                self.handle_ptr_instruction(instr, &function.name);
            }

            Instruction::BitCast(BitCast { operand, dest, .. })
            | Instruction::AddrSpaceCast(AddrSpaceCast { operand, dest, .. }) => {
                if let Some((value, _)) = get_operand_ident_type(operand, function) {
                    let dest = VarIdent::new_local(dest, function);
                    let instr = PointerInstruction::Assign { dest, value };
                    self.handle_ptr_instruction(instr, &function.name);
                };
            }

            // Instruction::GetElementPtr(_) => todo!(),
            // Instruction::IntToPtr(_) => todo!(),
            Instruction::Phi(Phi {
                incoming_values,
                dest,
                ..
            }) => {
                let incoming_values = incoming_values
                    .iter()
                    .filter_map(|(value, _)| get_operand_ident_type(value, function))
                    .map(|(name, _)| name)
                    .collect();

                let dest = VarIdent::new_local(dest, function);
                let instr = PointerInstruction::Phi {
                    dest,
                    incoming_values,
                };
                self.handle_ptr_instruction(instr, &function.name);
            }

            Instruction::Load(Load { address, dest, .. }) => {
                match get_operand_ident_type(address, function) {
                    Some((address, address_ty)) if is_ptr_type(address_ty) => {
                        let dest = VarIdent::new_local(dest, function);
                        let instr = PointerInstruction::Load { dest, address };
                        self.handle_ptr_instruction(instr, &function.name);
                    }
                    _ => {}
                }
            }

            // *x = y
            Instruction::Store(Store { address, value, .. }) => {
                let value = match get_operand_ident_type(value, function) {
                    Some((ident, _)) => ident,
                    _ => return,
                };
                if let Some((address, _)) = get_operand_ident_type(address, function) {
                    let instr = PointerInstruction::Store { address, value };
                    self.handle_ptr_instruction(instr, &function.name);
                }
            }

            // Instruction::Select(_) => todo!(),
            // Instruction::Freeze(_) => todo!(),
            Instruction::Call(Call {
                function: callee,
                arguments,
                dest,
                ..
            }) => self.handle_call(callee, arguments, dest.as_ref(), context),

            // Instruction::VAArg(_) => todo!(),
            _ => {}
        }
    }

    fn handle_terminator(
        &mut self,
        term: &'a Terminator,
        context @ Context {
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
            }) => self.handle_call(function, arguments, Some(result), context),

            Terminator::Ret(Ret { return_operand, .. }) => {
                let return_reg = match return_operand
                    .as_ref()
                    .and_then(|op| get_operand_ident_type(op, context_fun))
                {
                    Some((name, _)) => name,
                    _ => return,
                };

                let instr = PointerInstruction::Return { return_reg };
                self.handle_ptr_instruction(instr, &context_fun.name);
            }

            _ => {}
        }
    }
}

fn is_ptr_type(ty: &TypeRef) -> bool {
    matches!(ty.as_ref(), Type::PointerType { .. })
}

fn get_operand_ident_type<'a>(
    operand: &'a Operand,
    function: &'a Function,
) -> Option<(VarIdent<'a>, &'a TypeRef)> {
    match operand {
        Operand::LocalOperand { name, ty } => match ty.as_ref() {
            Type::PointerType { pointee_type, .. } => {
                Some((VarIdent::new_local(name, function), pointee_type))
            }
            _ => None,
        },
        Operand::ConstantOperand(constant) => match constant.as_ref() {
            llvm_ir::Constant::GlobalReference { name, ty } => {
                Some((VarIdent::Global { name }, ty))
            }
            _ => None,
        },
        Operand::MetadataOperand => None,
    }
}
