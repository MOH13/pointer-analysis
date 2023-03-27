use std::fmt::{self, Display, Formatter};
use std::ops::Deref;
use std::rc::Rc;

use either::Either;
use hashbrown::HashMap;
use llvm_ir::function::ParameterAttribute;
use llvm_ir::instruction::{
    AddrSpaceCast, Alloca, BitCast, Call, GetElementPtr, InlineAssembly, Load, Phi, Store,
};
use llvm_ir::module::GlobalVariable;
use llvm_ir::terminator::{Invoke, Ret};
use llvm_ir::types::NamedStructDef;
use llvm_ir::{
    constant, BasicBlock, Constant, Function, Instruction, Module, Name, Operand, Terminator, Type,
    TypeRef,
};

type StructMap<'a> = HashMap<&'a String, Rc<StructType>>;

#[derive(Copy, Clone)]
pub struct Context<'a, 'b> {
    pub module: &'a Module,
    pub function: &'a Function,
    pub block: &'a BasicBlock,
    pub structs: &'b StructMap<'a>,
}

/// This trait allows implementors to define the `handle_instruction` and `handle_terminator` functions,
/// which the `visit_module` function will call on all instructions and terminators.
pub trait ModuleVisitor<'a> {
    fn handle_function(&mut self, function: &'a Function, module: &'a Module);
    fn handle_global(&mut self, global: &'a GlobalVariable, module: &'a Module);
    fn handle_instruction(&mut self, instr: &'a Instruction, context: Context<'a, '_>);
    fn handle_terminator(&mut self, term: &'a Terminator, context: Context<'a, '_>);

    fn visit_module(&mut self, module: &'a Module) {
        let mut structs = HashMap::new();
        for (name, ty) in module
            .types
            .all_struct_names()
            .filter_map(|name| get_struct_from_name(name, module).map(|t| (name, t)))
        {
            StructType::add_to_structs(name, ty, &mut structs, module);
        }

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
                    structs: &structs,
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

#[derive(Clone, Debug)]
pub struct StructField {
    st: Rc<StructType>,
    degree: usize,
}

impl Deref for StructField {
    type Target = StructType;

    fn deref(&self) -> &Self::Target {
        &self.st
    }
}

#[derive(Clone, Debug)]
pub struct StructType {
    pub fields: Vec<Option<StructField>>,
}

impl StructType {
    fn add_to_structs<'a>(
        name: &'a String,
        ty: &'a TypeRef,
        structs: &mut StructMap<'a>,
        module: &'a Module,
    ) {
        let fields = match ty.as_ref() {
            Type::StructType { element_types, .. } => element_types,
            _ => panic!("ty should only be a StructType"),
        };
        let fields = fields
            .iter()
            .map(|f| {
                let (ty, degree) = strip_array_types(f);
                match ty.as_ref() {
                    Type::NamedStructType { name } => Some(StructField {
                        st: Self::lookup_or_new(name, structs, module),
                        degree,
                    }),
                    _ => None,
                }
            })
            .collect();
        structs.insert(name, Rc::new(Self { fields }));
    }

    fn lookup_or_new<'a>(
        name: &'a String,
        structs: &mut StructMap<'a>,
        module: &'a Module,
    ) -> Rc<StructType> {
        match structs.get(name) {
            Some(st) => Rc::clone(st),
            None => {
                let ty = get_struct_from_name(name, module).expect("struct was not defined");
                Self::add_to_structs(name, ty, structs, module);
                Rc::clone(&structs[name])
            }
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
    Alloca {
        dest: VarIdent<'a>,
        struct_type: Option<Rc<StructType>>,
    },
    /// x = malloc()
    Malloc { dest: VarIdent<'a> },
    /// x = gep y, o1, o2, ..
    Gep {
        dest: VarIdent<'a>,
        address: VarIdent<'a>,
        indices: Vec<usize>,
        struct_type: Rc<StructType>,
    },
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

#[derive(Clone, Copy)]
pub struct PointerContext<'a> {
    pub fun_name: &'a str,
}

pub trait PointerModuleVisitor<'a> {
    fn handle_ptr_function(&mut self, name: &'a str, parameters: Vec<VarIdent<'a>>);
    fn handle_ptr_global(&mut self, ident: VarIdent<'a>, init_ref: Option<VarIdent<'a>>);
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
        Context {
            function: caller, ..
        }: Context<'a, '_>,
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

        let context = PointerContext {
            fun_name: &caller.name,
        };

        let dest = match ty.as_ref() {
            Type::FuncType { result_type, .. } if is_ptr_type(result_type) => {
                dest.map(|d| VarIdent::new_local(d, caller))
            }
            _ => None,
        };

        // TODO: What if someone defines their own function called malloc?
        //       Maybe look at function signature?
        let instr = if function == "malloc" && dest.is_some() {
            PointerInstruction::Malloc {
                dest: dest.unwrap(),
            }
        } else {
            let arguments = arguments
                .iter()
                .map(|(arg, _)| get_operand_ident_type(arg, caller).map(|(ident, _, _)| ident))
                .collect();

            PointerInstruction::Call {
                dest,
                function,
                arguments,
            }
        };

        self.handle_ptr_instruction(instr, context);
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
        context @ Context { function, .. }: Context<'a, '_>,
    ) {
        let pointer_context = PointerContext {
            fun_name: &function.name,
        };
        match instr {
            // Instruction::ExtractElement(_) => todo!(),
            // Instruction::ExtractValue(_) => todo!(),
            Instruction::Alloca(Alloca {
                dest,
                allocated_type,
                ..
            }) => {
                let dest = VarIdent::new_local(dest, function);
                let struct_type = get_struct_type(allocated_type, context);
                let instr = PointerInstruction::Alloca { dest, struct_type };
                self.handle_ptr_instruction(instr, pointer_context);
            }

            Instruction::BitCast(BitCast { operand, dest, .. })
            | Instruction::AddrSpaceCast(AddrSpaceCast { operand, dest, .. }) => {
                if let Some((value, _, _)) = get_operand_ident_type(operand, function) {
                    let dest = VarIdent::new_local(dest, function);
                    let instr = PointerInstruction::Assign { dest, value };
                    self.handle_ptr_instruction(instr, pointer_context);
                };
            }

            Instruction::GetElementPtr(GetElementPtr {
                address,
                indices,
                dest,
                ..
            }) => {
                let (address, ty, degree) =
                    get_operand_ident_type(address, function).expect(&format!(
                    "GEP address should always be a pointer or array of pointers, got {address}"
                ));
                let dest = VarIdent::new_local(dest, function);

                let instr = match get_struct_type(ty, context) {
                    Some(struct_type) if indices.len() > degree => {
                        let mut reduced_indices = vec![];
                        let mut sub_struct_type = struct_type.as_ref();
                        let mut remaining_indices = &indices[degree..];
                        loop {
                            // All indices into structs must be constant i32
                            let i = match &remaining_indices[0] {
                                Operand::ConstantOperand(c) => match c.as_ref() {
                                    Constant::Int { value, .. } => *value as usize,
                                    _ => panic!("All indices into structs should be constant i32"),
                                },
                                _ => continue,
                            };

                            reduced_indices.push(i);

                            match &sub_struct_type.fields[i] {
                                Some(f) if remaining_indices.len() > f.degree + 1 => {
                                    sub_struct_type = f;
                                    remaining_indices = &remaining_indices[f.degree + 1..];
                                }
                                _ => break,
                            }
                        }

                        PointerInstruction::Gep {
                            dest,
                            address,
                            indices: reduced_indices,
                            struct_type: struct_type,
                        }
                    }

                    _ => PointerInstruction::Assign {
                        dest,
                        value: address,
                    },
                };

                self.handle_ptr_instruction(instr, pointer_context);
            }

            // Instruction::IntToPtr(_) => todo!(),
            Instruction::Phi(Phi {
                incoming_values,
                dest,
                ..
            }) => {
                let incoming_values = incoming_values
                    .iter()
                    .filter_map(|(value, _)| get_operand_ident_type(value, function))
                    .map(|(name, _, _)| name)
                    .collect();

                let dest = VarIdent::new_local(dest, function);
                let instr = PointerInstruction::Phi {
                    dest,
                    incoming_values,
                };
                self.handle_ptr_instruction(instr, pointer_context);
            }

            Instruction::Load(Load { address, dest, .. }) => {
                match get_operand_ident_type(address, function) {
                    Some((address, address_ty, _)) if is_ptr_type(address_ty) => {
                        let dest = VarIdent::new_local(dest, function);
                        let instr = PointerInstruction::Load { dest, address };
                        self.handle_ptr_instruction(instr, pointer_context);
                    }
                    _ => {}
                }
            }

            // *x = y
            Instruction::Store(Store { address, value, .. }) => {
                let value = match get_operand_ident_type(value, function) {
                    Some((ident, _, _)) => ident,
                    _ => return,
                };
                if let Some((address, _, _)) = get_operand_ident_type(address, function) {
                    let instr = PointerInstruction::Store { address, value };
                    self.handle_ptr_instruction(instr, pointer_context);
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
        }: Context<'a, '_>,
    ) {
        let pointer_context = PointerContext {
            fun_name: &context_fun.name,
        };
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
                    Some((name, _, _)) => name,
                    _ => return,
                };

                let instr = PointerInstruction::Return { return_reg };
                self.handle_ptr_instruction(instr, pointer_context);
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
) -> Option<(VarIdent<'a>, &'a TypeRef, usize)> {
    match operand {
        Operand::LocalOperand { name, ty } => {
            let (ty, degree) = strip_array_types(ty);
            match ty.as_ref() {
                Type::PointerType { pointee_type, .. } => Some((
                    VarIdent::new_local(name, function),
                    pointee_type,
                    degree + 1,
                )),
                _ => None,
            }
        }
        Operand::ConstantOperand(constant) => match constant.as_ref() {
            Constant::GlobalReference { name, ty } => Some((VarIdent::Global { name }, ty, 1)),
            Constant::BitCast(constant::BitCast { operand, to_type }) => {
                match (operand.as_ref(), to_type.as_ref()) {
                    (
                        Constant::GlobalReference { name, .. },
                        Type::PointerType { pointee_type, .. },
                    ) => Some((VarIdent::Global { name: name }, pointee_type, 1)),
                    _ => None,
                }
            }
            _ => None,
        },
        Operand::MetadataOperand => None,
    }
}

fn get_struct_type<'a>(ty: &'a TypeRef, context: Context<'a, '_>) -> Option<Rc<StructType>> {
    match ty.as_ref() {
        Type::NamedStructType { name } => context.structs.get(name).cloned(),
        _ => None,
    }
}

fn strip_array_types(ty: &TypeRef) -> (&TypeRef, usize) {
    match ty.as_ref() {
        Type::ArrayType { element_type, .. } | Type::VectorType { element_type, .. } => {
            let (ty, degree) = strip_array_types(element_type);
            (ty, degree + 1)
        }
        _ => (ty, 0),
    }
}

fn get_struct_from_name<'a>(name: &str, Module { types, .. }: &'a Module) -> Option<&'a TypeRef> {
    types.named_struct_def(name).and_then(|def| match def {
        NamedStructDef::Opaque => None,
        NamedStructDef::Defined(ty) => Some(ty),
    })
}
