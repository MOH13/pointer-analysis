use std::borrow::Cow;
use std::rc::Rc;

use either::Either;
use hashbrown::HashMap;
use llvm_ir::function::ParameterAttribute;
use llvm_ir::instruction::{
    AddrSpaceCast, Alloca, BitCast, Call, GetElementPtr, InlineAssembly, Load, Phi, Store,
};
use llvm_ir::module::GlobalVariable;
use llvm_ir::terminator::{Invoke, Ret};
use llvm_ir::{
    constant, Constant, Function, Instruction, Module, Name, Operand, Terminator, Type, TypeRef,
};

use super::structs::{count_flattened_fields, get_struct_type};
use super::{strip_array_types, Context, ModuleVisitor, StructMap, StructType, VarIdent};

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
        struct_type: Option<Rc<StructType>>, // If none, perform 'flat' gep
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

pub struct PointerModuleVisitor<'a, 'b, O> {
    original_ptr_types: HashMap<VarIdent<'a>, Rc<StructType>>,
    fresh_counter: usize,
    observer: &'b mut O,
}

impl<'a, 'b, O> PointerModuleVisitor<'a, 'b, O>
where
    O: PointerModuleObserver<'a>,
{
    pub fn new(observer: &'b mut O) -> Self {
        Self {
            original_ptr_types: HashMap::new(),
            fresh_counter: 0,
            observer,
        }
    }

    fn add_fresh_ident(&mut self) -> VarIdent<'a> {
        let ident = VarIdent::Fresh {
            index: self.fresh_counter,
        };
        self.fresh_counter = self.fresh_counter + 1;
        ident
    }

    fn get_original_type(
        &self,
        operand: &'a Operand,
        function: &'a Function,
    ) -> Option<(VarIdent<'a>, Rc<StructType>)> {
        if let Some((ident, _, _)) = get_operand_ident_type(operand, function) {
            return self
                .original_ptr_types
                .get(&ident)
                .map(|orig_ty| (ident, orig_ty.clone()));
        }
        None
    }

    fn handle_call(
        &mut self,
        function: &'a Either<InlineAssembly, Operand>,
        arguments: &'a [(Operand, Vec<ParameterAttribute>)],
        dest: Option<&'a Name>,
        context: Context<'a, '_>,
    ) {
        let caller = context.function;
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

        self.observer.handle_ptr_instruction(instr, context);
    }
}

impl<'a, 'b, O> ModuleVisitor<'a> for PointerModuleVisitor<'a, 'b, O>
where
    O: PointerModuleObserver<'a>,
{
    fn handle_function(&mut self, function: &'a Function, _module: &'a Module) {
        let parameters = function
            .parameters
            .iter()
            .map(|p| VarIdent::new_local(&p.name, function))
            .collect();
        self.observer
            .handle_ptr_function(&function.name, parameters)
    }

    fn handle_global(&mut self, global: &'a GlobalVariable, structs: &StructMap) {
        let init_ref = global
            .initializer
            .as_ref()
            .and_then(|init| match init.as_ref() {
                Constant::GlobalReference { name, .. } => Some(VarIdent::Global {
                    name: Cow::Borrowed(name),
                }),
                _ => None,
            });
        let struct_type = get_struct_type(&global.ty, structs);
        self.observer.handle_ptr_global(
            VarIdent::Global {
                name: Cow::Borrowed(&global.name),
            },
            init_ref,
            struct_type.as_deref(),
        );
    }

    fn handle_instruction(&mut self, instr: &'a Instruction, context: Context<'a, '_>) {
        let function = context.function;
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
                let struct_type = get_struct_type(allocated_type, context.structs);
                let instr = PointerInstruction::Alloca { dest, struct_type };
                self.observer.handle_ptr_instruction(instr, pointer_context);
            }

            Instruction::BitCast(BitCast { operand, dest, .. })
            | Instruction::AddrSpaceCast(AddrSpaceCast { operand, dest, .. }) => {
                if let Some((value, src_ty, _)) = get_operand_ident_type(operand, function) {
                    let dest = VarIdent::new_local(dest, function);
                    let instr = PointerInstruction::Assign {
                        dest: dest.clone(),
                        value: value.clone(),
                    };
                    self.observer.handle_ptr_instruction(instr, pointer_context);
                    if let Some(typ) = self.original_ptr_types.get(&value) {
                        self.original_ptr_types.insert(dest.clone(), typ.clone());
                    } else if let Some(struct_ty) = get_struct_type(src_ty, context.structs) {
                        self.original_ptr_types.insert(dest.clone(), struct_ty);
                    }
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

                let instr = match get_struct_type(ty, context.structs) {
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
                            struct_type: Some(struct_type),
                        }
                    }

                    _ => PointerInstruction::Assign {
                        dest,
                        value: address,
                    },
                };

                self.observer.handle_ptr_instruction(instr, pointer_context);
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
                self.observer.handle_ptr_instruction(instr, pointer_context);
            }

            Instruction::Load(Load { address, dest, .. }) => {
                match get_operand_ident_type(address, function) {
                    Some((address, address_ty, _)) if is_ptr_type(address_ty) => {
                        let dest = VarIdent::new_local(dest, function);
                        let instr = PointerInstruction::Load { dest, address };
                        self.observer.handle_ptr_instruction(instr, pointer_context);
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
                    self.observer.handle_ptr_instruction(instr, pointer_context);
                }
            }

            // Instruction::Select(_) => todo!(),
            // Instruction::Freeze(_) => todo!(),
            Instruction::Call(Call {
                function: callee,
                arguments,
                dest,
                ..
            }) => {
                // Special behavior for struct assignments (that are compiled to memcpy)
                if let Either::Right(Operand::ConstantOperand(constant)) = callee {
                    if let Constant::GlobalReference {
                        name: Name::Name(name),
                        ..
                    } = constant.as_ref()
                    {
                        if name.as_ref() == "llvm.memcpy.p0i8.p0i8.i64" {
                            match (
                                self.get_original_type(&arguments[0].0, function),
                                self.get_original_type(&arguments[1].0, function),
                            ) {
                                // Assume src_ty and dst_ty are same
                                (Some((dst_ident, _)), Some((src_ident, src_ty))) => {
                                    let num_cells = count_flattened_fields(src_ty.as_ref());
                                    for i in 0..num_cells {
                                        let src_gep_ident = self.add_fresh_ident();
                                        let dst_gep_ident = self.add_fresh_ident();
                                        let src_load_ident = self.add_fresh_ident();
                                        let src_gep = PointerInstruction::Gep {
                                            dest: src_gep_ident.clone(),
                                            address: src_ident.clone(),
                                            indices: vec![i],
                                            struct_type: None,
                                        };
                                        let dst_gep = PointerInstruction::Gep {
                                            dest: dst_gep_ident.clone(),
                                            address: dst_ident.clone(),
                                            indices: vec![i],
                                            struct_type: None,
                                        };
                                        let src_load = PointerInstruction::Load {
                                            dest: src_load_ident.clone(),
                                            address: src_gep_ident,
                                        };
                                        let dst_store = PointerInstruction::Store {
                                            address: dst_gep_ident,
                                            value: src_load_ident,
                                        };
                                        self.observer
                                            .handle_ptr_instruction(src_gep, pointer_context);
                                        self.observer
                                            .handle_ptr_instruction(dst_gep, pointer_context);
                                        self.observer
                                            .handle_ptr_instruction(src_load, pointer_context);
                                        self.observer
                                            .handle_ptr_instruction(dst_store, pointer_context);
                                    }
                                }
                                _ => (),
                            }
                        }
                    }
                }
                self.handle_call(callee, arguments, dest.as_ref(), context)
            }

            // Instruction::VAArg(_) => todo!(),
            _ => {}
        }
    }

    fn handle_terminator(&mut self, term: &'a Terminator, context: Context<'a, '_>) {
        let context_fun = context.function;
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
                self.observer.handle_ptr_instruction(instr, pointer_context);
            }

            _ => {}
        }
    }
}

pub trait PointerModuleObserver<'a> {
    fn handle_ptr_function(&mut self, name: &'a str, parameters: Vec<VarIdent<'a>>);
    fn handle_ptr_global(
        &mut self,
        ident: VarIdent<'a>,
        init_ref: Option<VarIdent<'a>>,
        struct_type: Option<&StructType>,
    );
    fn handle_ptr_instruction(
        &mut self,
        instr: PointerInstruction<'a>,
        context: PointerContext<'a>,
    );
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
            Constant::GlobalReference { name, ty } => Some((
                VarIdent::Global {
                    name: Cow::Borrowed(name),
                },
                ty,
                1,
            )),
            Constant::BitCast(constant::BitCast { operand, to_type }) => {
                match (operand.as_ref(), to_type.as_ref()) {
                    (
                        Constant::GlobalReference { name, .. },
                        Type::PointerType { pointee_type, .. },
                    ) => Some((
                        VarIdent::Global {
                            name: Cow::Borrowed(name),
                        },
                        pointee_type,
                        1,
                    )),
                    _ => None,
                }
            }
            _ => None,
        },
        Operand::MetadataOperand => None,
    }
}
