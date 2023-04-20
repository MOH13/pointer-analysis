use std::borrow::Cow;
use std::rc::Rc;

use either::Either;
use hashbrown::HashMap;
use llvm_ir::function::ParameterAttribute;
use llvm_ir::instruction::{
    AddrSpaceCast, Alloca, BitCast, Call, ExtractElement, Freeze, GetElementPtr, InlineAssembly,
    InsertElement, InsertValue, Load, Phi, Select, ShuffleVector, Store,
};
use llvm_ir::module::GlobalVariable;
use llvm_ir::terminator::{Invoke, Ret};
use llvm_ir::{
    constant, Constant, ConstantRef, Function, Instruction, Module, Name, Operand, Terminator,
    Type, TypeRef,
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
        struct_type: Option<Rc<StructType<'a>>>,
    },
    /// x = malloc()
    Malloc { dest: VarIdent<'a> },
    /// x = gep y, o1, o2, ..
    Gep {
        dest: VarIdent<'a>,
        address: VarIdent<'a>,
        indices: Vec<usize>,
        struct_type: Option<Rc<StructType<'a>>>, // If none, perform 'flat' gep
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
    pub fun_name: Option<&'a str>,
}

pub struct PointerModuleVisitor<'a, 'b, O> {
    original_ptr_types: HashMap<VarIdent<'a>, Rc<StructType<'a>>>,
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
        &mut self,
        operand: &'a Operand,
        function: &'a Function,
        context: Context<'a, '_>,
    ) -> Option<(VarIdent<'a>, Rc<StructType<'a>>)> {
        if let Some((ident, ..)) = self.get_operand_ident_type(operand, function, context) {
            return self
                .original_ptr_types
                .get(&ident)
                .map(|orig_ty| (ident, orig_ty.clone()));
        }
        None
    }

    fn unroll_constant(
        &mut self,
        constant: &'a ConstantRef,
        context: Context<'a, '_>,
    ) -> Option<(VarIdent<'a>, &'a TypeRef, usize)> {
        let pointer_context = PointerContext {
            fun_name: Some(&context.function.name),
        };

        match constant.as_ref() {
            Constant::Struct { .. } => {
                println!("Warning: Unhandled struct initializer");
                None
            }

            Constant::Array { elements, .. } | Constant::Vector(elements) => {
                let mut fresh = None;
                let mut degree = 0;
                let mut ty = None;

                for element in elements {
                    let (e, t, d) = match self.unroll_constant(element, context) {
                        Some(res) => res,
                        None => continue,
                    };
                    (ty, degree) = (Some(t), d);

                    let dest = fresh.get_or_insert_with(|| self.add_fresh_ident()).clone();
                    let instr = PointerInstruction::Assign { dest, value: e };
                    self.observer.handle_ptr_instruction(instr, pointer_context);
                }

                fresh.and_then(|f| ty.map(|t| (f, t, degree + 1)))
            }

            Constant::GlobalReference { name, ty } => Some((
                VarIdent::Global {
                    name: Cow::Borrowed(name),
                },
                ty,
                1,
            )),

            Constant::ExtractElement(constant::ExtractElement {
                vector: operand, ..
            })
            | Constant::AddrSpaceCast(constant::AddrSpaceCast { operand, .. }) => {
                self.unroll_constant(operand, context)
            }

            Constant::BitCast(constant::BitCast { operand, to_type }) => self
                .unroll_constant(operand, context)
                .map(|(ident, _, d)| (ident, to_type, d)),

            Constant::InsertElement(constant::InsertElement {
                vector: x,
                element: y,
                ..
            })
            | Constant::Select(constant::Select {
                true_value: x,
                false_value: y,
                ..
            })
            | Constant::ShuffleVector(constant::ShuffleVector {
                operand0: x,
                operand1: y,
                ..
            }) => {
                if let Some((x, tx, dx)) = self.unroll_constant(x, context) {
                    if let Some((y, _, dy)) = self.unroll_constant(y, context) {
                        let fresh = self.add_fresh_ident();
                        self.handle_join(fresh.clone(), x, y, pointer_context);
                        return Some((fresh, tx, dx.max(dy)));
                    }
                }

                None
            }

            Constant::ExtractValue(constant::ExtractValue { aggregate, indices }) => {
                if indices.len() != 1 {
                    println!("Warning: Unhandled ExtractValue");
                    return None;
                }

                println!("Warning: Potentially unhandled ExtractValue");
                self.unroll_constant(aggregate, context)
            }

            Constant::InsertValue(constant::InsertValue {
                aggregate,
                element,
                indices,
            }) => {
                if indices.len() != 1 {
                    println!("Warning: Unhandled InsertValue");
                    return None;
                }

                println!("Warning: Potentially unhandled InsertValue");
                if let Some((aggregate, ty, d)) = self.unroll_constant(aggregate, context) {
                    let fresh = self.add_fresh_ident();
                    if let Some((element, ..)) = self.unroll_constant(element, context) {
                        self.handle_join(fresh.clone(), aggregate, element, pointer_context);
                        return Some((fresh, ty, d));
                    }
                }

                None
            }

            Constant::GetElementPtr(constant::GetElementPtr {
                address, indices, ..
            }) => {
                let fresh = self.add_fresh_ident();
                if let Some((address, ty, degree)) = self.unroll_constant(address, context) {
                    let indices: Vec<_> = indices
                        .iter()
                        .map(|constant| match constant.as_ref() {
                            Constant::Int { value, .. } => Some(*value as usize),
                            _ => None,
                        })
                        .collect();

                    let (sub_ty, sub_degree) =
                        self.handle_gep(fresh.clone(), address, &indices, degree, ty, context);
                    return Some((fresh, sub_ty, sub_degree + 1));
                }
                None
            }

            Constant::IntToPtr(_) => {
                println!("Warning: IntToPtr detected");
                None
            }

            _ => None,
        }
    }

    fn get_operand_ident_type(
        &mut self,
        operand: &'a Operand,
        function: &'a Function,
        context: Context<'a, '_>,
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
            Operand::ConstantOperand(constant) => self.unroll_constant(constant, context),
            Operand::MetadataOperand => None,
        }
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

        let pointer_context = PointerContext {
            fun_name: Some(&caller.name),
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
                .map(|(arg, _)| {
                    self.get_operand_ident_type(arg, caller, context)
                        .map(|(ident, _, _)| ident)
                })
                .collect();

            PointerInstruction::Call {
                dest,
                function,
                arguments,
            }
        };

        self.observer.handle_ptr_instruction(instr, pointer_context);
    }

    fn handle_join(
        &mut self,
        dest: VarIdent<'a>,
        x: VarIdent<'a>,
        y: VarIdent<'a>,
        context: PointerContext<'a>,
    ) {
        let x_instr = PointerInstruction::Assign {
            dest: dest.clone(),
            value: x,
        };
        let y_instr = PointerInstruction::Assign { dest, value: y };
        self.observer.handle_ptr_instruction(x_instr, context);
        self.observer.handle_ptr_instruction(y_instr, context);
    }

    fn handle_gep(
        &mut self,
        dest: VarIdent<'a>,
        address: VarIdent<'a>,
        indices: &[Option<usize>],
        degree: usize,
        ty: &'a TypeRef,
        context: Context<'a, '_>,
    ) -> (&'a TypeRef, usize) {
        let pointer_context = PointerContext {
            fun_name: Some(&context.function.name),
        };

        let struct_type = get_struct_type(ty, context.structs);
        match struct_type {
            Some((struct_type, s_degree)) if indices.len() > degree + s_degree => {
                let mut reduced_indices = vec![];
                let mut sub_struct_type = struct_type.as_ref();
                let mut sub_ty;
                let mut sub_degree;
                let mut remaining_indices = &indices[degree + s_degree..];
                loop {
                    let i = remaining_indices[0]
                        .expect("all indices into structs must be constant i32");
                    reduced_indices.push(i);

                    let field = &sub_struct_type.fields[i];
                    sub_ty = field.ty;
                    sub_degree = field.degree;
                    match &field.st {
                        Some(st) if remaining_indices.len() > field.degree + 1 => {
                            sub_struct_type = st.as_ref();
                            remaining_indices = &remaining_indices[field.degree + 1..];
                        }
                        _ => break,
                    }
                }

                let instr = PointerInstruction::Gep {
                    dest,
                    address,
                    indices: reduced_indices,
                    struct_type: Some(struct_type),
                };
                self.observer.handle_ptr_instruction(instr, pointer_context);
                (sub_ty, sub_degree)
            }

            _ => {
                let instr = PointerInstruction::Assign {
                    dest,
                    value: address,
                };
                self.observer.handle_ptr_instruction(instr, pointer_context);
                (ty, degree)
            }
        }
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

    fn handle_global(&mut self, global: &'a GlobalVariable, structs: &StructMap<'a>) {
        let init_ref = global
            .initializer
            .as_ref()
            .and_then(|init| match init.as_ref() {
                Constant::GlobalReference { name, .. } => Some(VarIdent::Global {
                    name: Cow::Borrowed(name),
                }),
                _ => None,
            });

        let ty = match global.ty.as_ref() {
            Type::PointerType { pointee_type, .. } if !global.is_constant => pointee_type,
            _ => &global.ty,
        };

        let struct_type = get_struct_type(ty, structs).map(|(s, _)| s);
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
            fun_name: Some(&function.name),
        };
        match instr {
            Instruction::ExtractElement(ExtractElement {
                vector: operand,
                dest,
                ..
            })
            | Instruction::Freeze(Freeze { operand, dest, .. }) => {
                if let Some((value, ..)) = self.get_operand_ident_type(operand, function, context) {
                    let dest = VarIdent::new_local(dest, function);
                    let instr = PointerInstruction::Assign { dest, value };
                    self.observer.handle_ptr_instruction(instr, pointer_context);
                }
            }

            Instruction::ExtractValue(_) => todo!(),

            Instruction::InsertElement(InsertElement {
                vector: x,
                element: y,
                dest,
                ..
            })
            | Instruction::Select(Select {
                true_value: x,
                false_value: y,
                dest,
                ..
            })
            | Instruction::ShuffleVector(ShuffleVector {
                operand0: x,
                operand1: y,
                dest,
                ..
            }) => {
                if let (Some((x, ..)), Some((y, ..))) = (
                    self.get_operand_ident_type(x, function, context),
                    self.get_operand_ident_type(y, function, context),
                ) {
                    let dest = VarIdent::new_local(dest, function);
                    self.handle_join(dest, x, y, pointer_context);
                }
            }

            Instruction::InsertValue(InsertValue {
                aggregate,
                element,
                indices,
                dest,
                ..
            }) => todo!(),

            Instruction::Alloca(Alloca {
                dest,
                allocated_type,
                ..
            }) => {
                let dest = VarIdent::new_local(dest, function);
                let struct_type = get_struct_type(allocated_type, context.structs).map(|(s, _)| s);
                let instr = PointerInstruction::Alloca { dest, struct_type };
                self.observer.handle_ptr_instruction(instr, pointer_context);
            }

            Instruction::BitCast(BitCast { operand, dest, .. })
            | Instruction::AddrSpaceCast(AddrSpaceCast { operand, dest, .. }) => {
                if let Some((value, src_ty, _)) =
                    self.get_operand_ident_type(operand, function, context)
                {
                    let dest = VarIdent::new_local(dest, function);
                    let instr = PointerInstruction::Assign {
                        dest: dest.clone(),
                        value: value.clone(),
                    };
                    self.observer.handle_ptr_instruction(instr, pointer_context);
                    if let Some(typ) = self.original_ptr_types.get(&value) {
                        self.original_ptr_types.insert(dest.clone(), typ.clone());
                    } else if let Some((struct_ty, _)) = get_struct_type(src_ty, context.structs) {
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
                let (address, ty, degree) = self
                    .get_operand_ident_type(address, function, context)
                    .expect(&format!(
                    "GEP address should always be a pointer or array of pointers, got {address}"
                ));
                let dest = VarIdent::new_local(dest, function);

                let indices: Vec<_> = indices
                    .iter()
                    .map(|op| match op {
                        Operand::ConstantOperand(constant) => match constant.as_ref() {
                            Constant::Int { value, .. } => Some(*value as usize),
                            _ => None,
                        },
                        _ => None,
                    })
                    .collect();

                self.handle_gep(dest, address, &indices, degree, ty, context);
            }

            Instruction::Phi(Phi {
                incoming_values,
                dest,
                ..
            }) => {
                let incoming_values = incoming_values
                    .iter()
                    .filter_map(|(value, _)| self.get_operand_ident_type(value, function, context))
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
                match self.get_operand_ident_type(address, function, context) {
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
                let value = match self.get_operand_ident_type(value, function, context) {
                    Some((ident, ..)) => ident,
                    _ => return,
                };
                if let Some((address, ..)) = self.get_operand_ident_type(address, function, context)
                {
                    let instr = PointerInstruction::Store { address, value };
                    self.observer.handle_ptr_instruction(instr, pointer_context);
                }
            }

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
                            let arg0 = self.get_original_type(&arguments[0].0, function, context);
                            let arg1 = self.get_original_type(&arguments[1].0, function, context);
                            match (arg0, arg1) {
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

            Instruction::VAArg(_) => println!("Warning: Unhandled VAArg"),

            _ => {}
        }
    }

    fn handle_terminator(&mut self, term: &'a Terminator, context: Context<'a, '_>) {
        let context_fun = context.function;
        let pointer_context = PointerContext {
            fun_name: Some(&context_fun.name),
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
                    .and_then(|op| self.get_operand_ident_type(op, context_fun, context))
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
        struct_type: Option<&StructType<'a>>,
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
