use std::borrow::Cow;
use std::rc::Rc;

use either::Either;
use hashbrown::HashMap;
use llvm_ir::function::ParameterAttribute;
use llvm_ir::instruction::{
    AddrSpaceCast, Alloca, BitCast, Call, ExtractElement, ExtractValue, Freeze, GetElementPtr,
    InlineAssembly, InsertElement, InsertValue, Load, Phi, Select, ShuffleVector, Store,
};
use llvm_ir::module::GlobalVariable;
use llvm_ir::terminator::{Invoke, Ret};
use llvm_ir::{
    constant, Constant, ConstantRef, Function, Instruction, Name, Operand, Terminator, Type,
    TypeRef,
};

use super::{
    strip_array_types, strip_pointer_type, Context, ModuleVisitor, StructMap, StructType, VarIdent,
};

#[derive(Debug)]
pub enum PointerInstruction<'a> {
    /// Used to simply register an ident
    Fresh {
        ident: VarIdent<'a>,
        struct_type: Option<Rc<StructType>>,
    },
    /// x = y
    Assign {
        dest: VarIdent<'a>,
        value: VarIdent<'a>,
        struct_type: Option<Rc<StructType>>,
    },
    /// *x = y
    Store {
        address: VarIdent<'a>,
        value: VarIdent<'a>,
        struct_type: Option<Rc<StructType>>,
    },
    /// x = *y
    Load {
        dest: VarIdent<'a>,
        address: VarIdent<'a>,
        struct_type: Option<Rc<StructType>>,
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
        struct_type: Option<Rc<StructType>>,
    },
    /// [x =] f(y1, y2, ..)
    Call {
        dest: Option<VarIdent<'a>>,
        function: VarIdent<'a>,
        arguments: Vec<Option<VarIdent<'a>>>,
        return_struct_type: Option<Rc<StructType>>,
    },
    /// return x
    Return { return_reg: VarIdent<'a> },
}

#[derive(Clone, Copy)]
pub struct PointerContext<'a> {
    pub fun_name: Option<&'a str>,
}

impl<'a> PointerContext<'a> {
    fn from_context(context: Context<'a, '_>) -> Self {
        Self {
            fun_name: context.function.map(|fun| fun.name.as_str()),
        }
    }
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
        &mut self,
        operand: &'a Operand,
        context: Context<'a, '_>,
    ) -> Option<(VarIdent<'a>, Rc<StructType>)> {
        if let Some((ident, ty, ..)) = self.get_operand_ident_type(operand, context) {
            let struct_type = self.original_ptr_types.get(&ident).cloned().or_else(|| {
                StructType::try_from_type(
                    strip_pointer_type(ty).expect("Expected operand to be a pointer"),
                    context.structs,
                )
            });
            return struct_type.map(|st| (ident, st));
        }
        None
    }

    fn unroll_constant(
        &mut self,
        constant: &'a ConstantRef,
        context: Context<'a, '_>,
    ) -> (Option<VarIdent<'a>>, TypeRef, usize) {
        let pointer_context = PointerContext::from_context(context);

        match constant.as_ref() {
            Constant::Struct { name, values, .. } => {
                let fresh = self.add_fresh_ident();
                let fresh_rc = Rc::new(fresh.clone());
                let mut value_types = Vec::with_capacity(values.len());
                for (i, val) in values.iter().enumerate() {
                    let (val, ty, _) = self.unroll_constant(val, context);
                    value_types.push(ty.clone());
                    let fresh_field = VarIdent::Offset {
                        base: fresh_rc.clone(),
                        offset: i,
                    };
                    let struct_type = StructType::try_from_type(ty, context.structs);
                    match val {
                        Some(val) => {
                            self.handle_assign(fresh_field, val, struct_type, pointer_context);
                        }
                        None => {
                            self.handle_unused_fresh(fresh_field, struct_type, pointer_context);
                        }
                    }
                }

                let ty = match name {
                    Some(name) => context.module.types.named_struct(name),
                    None => context.module.types.struct_of(value_types, false),
                };
                (Some(fresh), ty, 0)
            }

            Constant::Array {
                elements,
                element_type,
            } => self.unroll_array(elements, Some(element_type.clone()), context),

            Constant::Vector(elements) => self.unroll_array(elements, None, context),

            Constant::GlobalReference { name, ty } => (
                Some(VarIdent::Global {
                    name: Cow::Borrowed(name),
                }),
                context.module.types.pointer_to(ty.clone()),
                0,
            ),

            Constant::ExtractElement(constant::ExtractElement {
                vector: operand, ..
            })
            | Constant::AddrSpaceCast(constant::AddrSpaceCast { operand, .. }) => {
                self.unroll_constant(operand, context)
            }

            Constant::BitCast(constant::BitCast { operand, .. }) => {
                let (ident, from_type, degree) = self.unroll_constant(operand, context);
                (ident, from_type, degree) // Notice that we return from_type!
            }

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
                let (x, tx, dx) = self.unroll_constant(x, context);
                let (y, ..) = self.unroll_constant(y, context);

                let struct_type = StructType::try_from_type(tx.clone(), context.structs);

                match (x, y) {
                    (Some(x), Some(y)) => {
                        let fresh = self.add_fresh_ident();
                        self.handle_join(fresh.clone(), x, y, struct_type, pointer_context);
                        (Some(fresh), tx, dx)
                    }
                    _ => (None, tx, dx),
                }
            }

            Constant::ExtractValue(constant::ExtractValue { aggregate, indices }) => {
                let (base, ty, degree) = self.unroll_constant(aggregate, context);
                match base {
                    Some(base) => {
                        let fresh = self.add_fresh_ident();
                        let (sub_ty, sub_degree) = self.handle_extract_value(
                            fresh.clone(),
                            base,
                            indices,
                            degree,
                            ty,
                            context,
                        );
                        (Some(fresh), sub_ty, sub_degree)
                    }
                    None => (None, ty, degree),
                }
            }

            Constant::InsertValue(constant::InsertValue {
                aggregate,
                element,
                indices,
            }) => {
                let (base, base_ty, base_degree) = self.unroll_constant(aggregate, context);
                let (value, ..) = self.unroll_constant(element, context);

                match (base, value) {
                    (Some(base), Some(value)) => {
                        let fresh = self.add_fresh_ident();
                        self.handle_insert_value(
                            fresh.clone(),
                            base,
                            value,
                            &indices,
                            base_degree,
                            base_ty.clone(),
                            context,
                        );
                        (Some(fresh), base_ty, base_degree)
                    }
                    // inserted element is irrelevant
                    (Some(base), None) => (Some(base), base_ty, base_degree),
                    // aggregate is an array of irrelevant type
                    (None, _) => (None, base_ty, base_degree),
                }
            }

            Constant::GetElementPtr(constant::GetElementPtr {
                address, indices, ..
            }) => {
                let (address, ty, degree) = self.unroll_constant(address, context);
                match address {
                    Some(address) => {
                        let fresh = self.add_fresh_ident();

                        let indices: Vec<_> = indices
                            .iter()
                            .map(|constant| match constant.as_ref() {
                                Constant::Int { value, .. } => Some(*value as usize),
                                _ => None,
                            })
                            .collect();

                        let (sub_ty, sub_degree) =
                            self.handle_gep(fresh.clone(), address, &indices, degree, ty, context);
                        (Some(fresh), sub_ty, sub_degree)
                    }
                    None => {
                        println!("Warning: GEP on a None value");
                        (None, ty, degree)
                    }
                }
            }

            Constant::IntToPtr(constant::IntToPtr { to_type, .. }) => {
                println!("Warning: IntToPtr detected");
                let fresh = self.add_fresh_ident();
                self.handle_unused_fresh(fresh.clone(), None, pointer_context);

                (Some(fresh), to_type.clone(), 0)
            }

            Constant::Poison(ty) => {
                let struct_type = StructType::try_from_type(ty.clone(), context.structs);
                let fresh = self.add_fresh_ident();
                self.handle_unused_fresh(fresh.clone(), struct_type, pointer_context);

                (Some(fresh), ty.clone(), 0)
            }

            Constant::Null(ty) => {
                let fresh = self.add_fresh_ident();
                self.handle_unused_fresh(fresh.clone(), None, pointer_context);

                (Some(fresh), ty.clone(), 0)
            }

            _ => (None, context.module.types.i8(), 0),
        }
    }

    fn unroll_array(
        &mut self,
        elements: &'a [ConstantRef],
        element_type: Option<TypeRef>,
        context: Context<'a, '_>,
    ) -> (Option<VarIdent<'a>>, TypeRef, usize) {
        let pointer_context = PointerContext::from_context(context);

        let mut fresh = None;
        let mut degree = 0;
        let mut ty = element_type.unwrap_or_else(|| context.module.types.void());

        for element in elements {
            if let (Some(e), t, d) = self.unroll_constant(element, context) {
                (ty, degree) = (t.clone(), d);

                let struct_type = StructType::try_from_type(t, context.structs);
                let dest = fresh.get_or_insert_with(|| self.add_fresh_ident());
                self.handle_assign(dest.clone(), e, struct_type, pointer_context);
            }
        }

        (fresh, ty, degree + 1)
    }

    fn get_operand_ident_type(
        &mut self,
        operand: &'a Operand,
        context: Context<'a, '_>,
    ) -> Option<(VarIdent<'a>, TypeRef, usize)> {
        let function = context
            .function
            .expect("Expected to be called in a function");
        match operand {
            Operand::LocalOperand { name, ty } => {
                let (ty, degree) = strip_array_types(ty.clone());
                match ty.as_ref() {
                    Type::PointerType { .. }
                    | Type::NamedStructType { .. }
                    | Type::StructType { .. } => {
                        Some((VarIdent::new_local(name, function), ty, degree))
                    }
                    _ => None,
                }
            }
            Operand::ConstantOperand(constant) => {
                let (ident, ty, degree) = self.unroll_constant(constant, context);
                ident.map(|id| (id, ty, degree))
            }
            Operand::MetadataOperand => {
                println!("Warning: Metadata operand");
                None
            }
        }
    }

    fn handle_unused_fresh(
        &mut self,
        ident: VarIdent<'a>,
        struct_type: Option<Rc<StructType>>,
        pointer_context: PointerContext<'a>,
    ) {
        let instr = PointerInstruction::Fresh {
            ident: ident,
            struct_type: struct_type,
        };
        self.observer.handle_ptr_instruction(instr, pointer_context);
    }

    fn handle_call(
        &mut self,
        function: &'a Either<InlineAssembly, Operand>,
        arguments: &'a [(Operand, Vec<ParameterAttribute>)],
        dest: Option<&'a Name>,
        context: Context<'a, '_>,
    ) {
        let caller = context
            .function
            .expect("Expected calls to happen in other calls");
        let pointer_context = PointerContext::from_context(context);

        // TODO: Filter out irrelevant function calls
        let (function, ty, _) = match function {
            Either::Right(op) => self
                .get_operand_ident_type(op, context)
                .expect("Functions should always be relevant"),
            _ => {
                println!("Warning: Inline assembly not handled");
                return;
            }
        };

        let result_ty = match strip_pointer_type(ty.clone())
            .expect("Functions should be pointer types")
            .as_ref()
        {
            Type::FuncType { result_type, .. } => strip_array_types(result_type.clone()).0,
            _ => panic!("Unexpected type {ty} of function {function}"),
        };
        let return_struct_type = StructType::try_from_type(result_ty.clone(), context.structs);

        let dest = if is_ptr_type(result_ty.clone()) || is_struct_type(result_ty) {
            dest.map(|d| VarIdent::new_local(d, caller))
        } else {
            None
        };

        if let VarIdent::Global { name } = &function {
            if let Name::Name(name) = name.as_ref() {
                if self.handle_special_function(name.as_str(), arguments, dest.clone(), context) {
                    return;
                }
            }
        }

        let arguments = arguments
            .iter()
            .map(|(arg, _)| {
                self.get_operand_ident_type(arg, context)
                    .map(|(ident, _, _)| ident)
            })
            .collect();

        let instr = PointerInstruction::Call {
            dest,
            function,
            arguments,
            return_struct_type,
        };

        self.observer.handle_ptr_instruction(instr, pointer_context);
    }

    /// Handle (possibly) special-case functions like malloc.
    ///
    /// Returns `true` if the function was special-case, `false` if not.
    fn handle_special_function(
        &mut self,
        function: &str,
        arguments: &'a [(Operand, Vec<ParameterAttribute>)],
        dest: Option<VarIdent<'a>>,
        context: Context<'a, '_>,
    ) -> bool {
        let pointer_context = PointerContext::from_context(context);

        match function {
            // Special behavior for struct assignments (that are compiled to memcpy)
            "llvm.memcpy.p0i8.p0i8.i64" => {
                let dest = self.get_original_type(&arguments[0].0, context);
                let src = self.get_original_type(&arguments[1].0, context);

                // Assume src_ty and dest_ty are same
                if let (Some((dest_ident, _)), Some((src_ident, src_ty))) = (dest, src) {
                    let intermediate_ident = self.add_fresh_ident();
                    let src_load = PointerInstruction::Load {
                        dest: intermediate_ident.clone(),
                        address: src_ident,
                        struct_type: Some(src_ty.clone()),
                    };
                    let dest_store = PointerInstruction::Store {
                        address: dest_ident,
                        value: intermediate_ident,
                        struct_type: Some(src_ty),
                    };
                    self.observer
                        .handle_ptr_instruction(src_load, pointer_context);
                    self.observer
                        .handle_ptr_instruction(dest_store, pointer_context);
                }

                true
            }

            // TODO: What if someone defines their own function called malloc?
            //       Maybe look at function signature?
            "malloc" => {
                let instr = PointerInstruction::Malloc {
                    dest: dest.expect("malloc should have a destination"),
                };
                self.observer.handle_ptr_instruction(instr, pointer_context);

                true
            }

            _ => false,
        }
    }

    fn handle_join(
        &mut self,
        dest: VarIdent<'a>,
        x: VarIdent<'a>,
        y: VarIdent<'a>,
        struct_type: Option<Rc<StructType>>,
        context: PointerContext<'a>,
    ) {
        self.handle_assign(dest.clone(), x, struct_type.clone(), context);
        self.handle_assign(dest.clone(), y, struct_type.clone(), context);
    }

    fn handle_assign(
        &mut self,
        dest: VarIdent<'a>,
        value: VarIdent<'a>,
        struct_type: Option<Rc<StructType>>,
        context: PointerContext<'a>,
    ) {
        let instr = PointerInstruction::Assign {
            dest,
            value,
            struct_type,
        };
        self.observer.handle_ptr_instruction(instr, context)
    }

    fn handle_extract_value(
        &mut self,
        dest: VarIdent<'a>,
        base: VarIdent<'a>,
        indices: &[u32],
        degree: usize,
        ty: TypeRef,
        context: Context<'a, '_>,
    ) -> (TypeRef, usize) {
        let pointer_context = PointerContext::from_context(context);

        match StructType::try_from_type_with_degree(ty.clone(), context.structs) {
            Some((st, 0)) if degree < indices.len() => {
                let (field_ident, field_ty, field_degree) =
                    get_field_ident_type(base, &*st, indices, degree);

                let field_st = StructType::try_from_type(field_ty.clone(), context.structs);
                self.handle_assign(dest, field_ident, field_st, pointer_context);
                (field_ty, field_degree)
            }
            // extracing a struct from an array
            Some((st, 0)) => {
                self.handle_assign(dest, base, Some(st), pointer_context);
                (ty, degree - indices.len())
            }
            // base should be pre-stripped of array types
            Some(_) => panic!("Type was an array type ({ty})"),
            _ => {
                self.handle_assign(dest, base, None, pointer_context);
                (ty, degree - indices.len())
            }
        }
    }

    fn handle_insert_value(
        &mut self,
        dest: VarIdent<'a>,
        base: VarIdent<'a>,
        value: VarIdent<'a>,
        indices: &[u32],
        base_degree: usize,
        base_ty: TypeRef,
        context: Context<'a, '_>,
    ) {
        let pointer_context = PointerContext::from_context(context);

        match StructType::try_from_type_with_degree(base_ty.clone(), context.structs) {
            Some((st, 0)) if base_degree < indices.len() => {
                self.handle_assign(dest.clone(), base, Some(st.clone()), pointer_context);

                let (field_ident, field_ty, _) =
                    get_field_ident_type(dest, &*st, indices, base_degree);
                let field_st = StructType::try_from_type(field_ty, context.structs);
                self.handle_assign(field_ident, value, field_st, pointer_context);
            }
            // inserting a struct into an array
            Some((st, 0)) => self.handle_join(dest, base, value, Some(st), pointer_context),
            // base should be pre-stripped of array types
            Some(_) => panic!("Type was an array type ({base_ty})"),
            None => self.handle_join(dest, base, value, None, pointer_context),
        }
    }

    fn handle_gep(
        &mut self,
        dest: VarIdent<'a>,
        address: VarIdent<'a>,
        indices: &[Option<usize>],
        degree: usize,
        ty: TypeRef,
        context: Context<'a, '_>,
    ) -> (TypeRef, usize) {
        let pointer_context = PointerContext::from_context(context);

        let stripped_ty =
            strip_pointer_type(ty.clone()).expect("GEP should only be used on pointer types");
        let indices = &indices[1..];

        let struct_type = StructType::try_from_type_with_degree(stripped_ty, context.structs);
        match struct_type {
            Some((struct_type, s_degree)) if indices.len() > degree + s_degree => {
                let (reduced_indices, field_ty, field_degree) =
                    get_reduced_indices(&*struct_type, indices, degree + s_degree);

                let instr = PointerInstruction::Gep {
                    dest,
                    address,
                    indices: reduced_indices,
                    struct_type: Some(struct_type),
                };
                self.observer.handle_ptr_instruction(instr, pointer_context);
                (context.module.types.pointer_to(field_ty), field_degree)
            }

            _ => {
                self.handle_assign(dest, address, None, pointer_context);
                (ty, degree)
            }
        }
    }
}

impl<'a, 'b, O> ModuleVisitor<'a> for PointerModuleVisitor<'a, 'b, O>
where
    O: PointerModuleObserver<'a>,
{
    fn init(&mut self, structs: &StructMap) {
        self.observer.init(structs)
    }

    fn handle_function(&mut self, function: &'a Function, context: Context<'a, '_>) {
        let ident = VarIdent::Global {
            name: Cow::Owned(Name::Name(Box::new(function.name.clone()))),
        };
        let parameters = function
            .parameters
            .iter()
            .map(|p| VarIdent::new_local(&p.name, function))
            .collect();
        let return_struct_type =
            StructType::try_from_type(function.return_type.clone(), context.structs);
        self.observer
            .handle_ptr_function(ident, parameters, return_struct_type);
    }

    fn handle_global(&mut self, global: &'a GlobalVariable, context: Context<'a, '_>) {
        let init_ref = global
            .initializer
            .as_ref()
            .and_then(|init| self.unroll_constant(init, context).0);

        let ty = match global.ty.as_ref() {
            Type::PointerType { pointee_type, .. } => pointee_type,
            _ => &global.ty,
        };

        let struct_type = StructType::try_from_type(ty.clone(), context.structs);
        self.observer.handle_ptr_global(
            VarIdent::Global {
                name: Cow::Borrowed(&global.name),
            },
            init_ref,
            struct_type,
        );
    }

    fn handle_instruction(&mut self, instr: &'a Instruction, context: Context<'a, '_>) {
        let function = context
            .function
            .expect("Expected to be called in a function");
        let pointer_context = PointerContext::from_context(context);
        match instr {
            Instruction::ExtractElement(ExtractElement {
                vector: operand,
                dest,
                ..
            })
            | Instruction::Freeze(Freeze { operand, dest, .. }) => {
                if let Some((value, ty, ..)) = self.get_operand_ident_type(operand, context) {
                    let dest = VarIdent::new_local(dest, function);
                    let struct_type = StructType::try_from_type(ty, context.structs);
                    self.handle_assign(dest, value, struct_type, pointer_context);
                }
            }

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
                let dest = VarIdent::new_local(dest, function);
                if let (Some((x, ty, ..)), Some((y, ..))) = (
                    self.get_operand_ident_type(x, context),
                    self.get_operand_ident_type(y, context),
                ) {
                    let struct_type = StructType::try_from_type(ty, context.structs);
                    self.handle_join(dest, x, y, struct_type, pointer_context);
                }
            }

            Instruction::ExtractValue(ExtractValue {
                aggregate,
                indices,
                dest,
                ..
            }) => {
                if let Some((base, ty, degree)) = self.get_operand_ident_type(aggregate, context) {
                    let dest = VarIdent::new_local(dest, function);
                    self.handle_extract_value(dest, base, indices, degree, ty, context);
                }
            }

            Instruction::InsertValue(InsertValue {
                aggregate,
                element,
                indices,
                dest,
                ..
            }) => {
                let dest = VarIdent::new_local(dest, function);
                match (
                    self.get_operand_ident_type(aggregate, context),
                    self.get_operand_ident_type(element, context),
                ) {
                    (Some((base, base_ty, base_degree)), Some((value, ..))) => self
                        .handle_insert_value(
                            dest,
                            base,
                            value,
                            &indices,
                            base_degree,
                            base_ty,
                            context,
                        ),
                    // inserted element is irrelevant
                    (Some((base, ty, _)), None) => {
                        let struct_type = StructType::try_from_type(ty, context.structs);
                        self.handle_assign(dest, base, struct_type, pointer_context);
                    }
                    // aggregate is an array of irrelevant type
                    // TODO: Do we need a Fresh instrcuction here>
                    (None, _) => {}
                }
            }

            Instruction::Alloca(Alloca {
                dest,
                allocated_type,
                ..
            }) => {
                let dest = VarIdent::new_local(dest, function);
                let struct_type =
                    StructType::try_from_type(allocated_type.clone(), context.structs);
                let instr = PointerInstruction::Alloca { dest, struct_type };
                self.observer.handle_ptr_instruction(instr, pointer_context);
            }

            Instruction::BitCast(BitCast { operand, dest, .. })
            | Instruction::AddrSpaceCast(AddrSpaceCast { operand, dest, .. }) => {
                if let Some((value, src_ty, _)) = self.get_operand_ident_type(operand, context) {
                    let src_ty = strip_pointer_type(src_ty)
                        .expect("bitcast and addrspacecast should only take pointer args");
                    let dest = VarIdent::new_local(dest, function);
                    let struct_type = StructType::try_from_type(src_ty.clone(), context.structs);

                    if let Some(st) = self.original_ptr_types.get(&value) {
                        self.original_ptr_types.insert(dest.clone(), st.clone());
                    } else if let Some(st) = struct_type {
                        self.original_ptr_types.insert(dest.clone(), st);
                    }

                    // Always a pointer type, so no struct type
                    self.handle_assign(dest, value, None, pointer_context);
                };
            }

            Instruction::GetElementPtr(GetElementPtr {
                address,
                indices,
                dest,
                ..
            }) => {
                let (address, ty, degree) =
                    self.get_operand_ident_type(address, context)
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
                let (incoming_values, incoming_types): (Vec<_>, Vec<_>) = incoming_values
                    .iter()
                    .filter_map(|(value, _)| self.get_operand_ident_type(value, context))
                    .map(|(ident, ty, _)| (ident, ty))
                    .unzip();

                let dest = VarIdent::new_local(dest, function);
                let struct_type = incoming_types
                    .first()
                    .and_then(|ty| StructType::try_from_type(ty.clone(), context.structs));
                let instr = PointerInstruction::Phi {
                    dest,
                    incoming_values,
                    struct_type,
                };
                self.observer.handle_ptr_instruction(instr, pointer_context);
            }

            Instruction::Load(Load { address, dest, .. }) => {
                match self.get_operand_ident_type(address, context) {
                    Some((address, address_ty, _)) if is_ptr_type(address_ty.clone()) => {
                        let dest = VarIdent::new_local(dest, function);
                        let struct_type = match address_ty.as_ref() {
                            Type::PointerType { pointee_type, .. } => {
                                StructType::try_from_type(pointee_type.clone(), context.structs)
                            }
                            _ => unreachable!(),
                        };
                        let instr = PointerInstruction::Load {
                            dest,
                            address,
                            struct_type,
                        };
                        self.observer.handle_ptr_instruction(instr, pointer_context);
                    }
                    _ => {}
                }
            }

            // *x = y
            Instruction::Store(Store { address, value, .. }) => {
                if let (Some((value, value_type, _)), Some((address, _, _))) = (
                    self.get_operand_ident_type(value, context),
                    self.get_operand_ident_type(address, context),
                ) {
                    let struct_type = StructType::try_from_type(value_type, context.structs);
                    let instr = PointerInstruction::Store {
                        address,
                        value,
                        struct_type,
                    };
                    self.observer.handle_ptr_instruction(instr, pointer_context);
                }
            }

            Instruction::Call(Call {
                function: callee,
                arguments,
                dest,
                ..
            }) => {
                self.handle_call(callee, arguments, dest.as_ref(), context);
            }

            _ => {}
        }
    }

    fn handle_terminator(&mut self, term: &'a Terminator, context: Context<'a, '_>) {
        let pointer_context = PointerContext::from_context(context);
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
                    .and_then(|op| self.get_operand_ident_type(op, context))
                {
                    Some((name, ..)) => name,
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
    fn init(&mut self, structs: &StructMap);
    fn handle_ptr_function(
        &mut self,
        name: VarIdent<'a>,
        parameters: Vec<VarIdent<'a>>,
        return_struct_type: Option<Rc<StructType>>,
    );
    fn handle_ptr_global(
        &mut self,
        ident: VarIdent<'a>,
        init_ref: Option<VarIdent<'a>>,
        struct_type: Option<Rc<StructType>>,
    );
    fn handle_ptr_instruction(
        &mut self,
        instr: PointerInstruction<'a>,
        context: PointerContext<'a>,
    );
}

fn get_reduced_indices(
    struct_type: &StructType,
    indices: &[Option<usize>],
    degree: usize,
) -> (Vec<usize>, TypeRef, usize) {
    let mut reduced_indices = vec![];
    let mut sub_struct_type = struct_type;
    let mut remaining_indices = &indices[degree..];
    loop {
        let i = remaining_indices[0].expect("all indices into structs must be constant i32");
        reduced_indices.push(i);

        let field = &sub_struct_type.fields[i];
        match &field.st {
            Some(st) if remaining_indices.len() > field.degree + 1 => {
                sub_struct_type = st.as_ref();
                remaining_indices = &remaining_indices[field.degree + 1..];
            }
            _ => {
                return (reduced_indices, field.ty.clone(), field.degree);
            }
        }
    }
}

fn get_field_ident_type<'a>(
    base: VarIdent<'a>,
    struct_type: &StructType,
    indices: &[u32],
    degree: usize,
) -> (VarIdent<'a>, TypeRef, usize) {
    let indices: Vec<_> = indices.iter().map(|&i| Some(i as usize)).collect();
    let (reduced_indices, field_ty, field_degree) =
        get_reduced_indices(struct_type, &indices, degree);
    let field_ident = reduced_indices
        .into_iter()
        .fold(base, |acc, i| VarIdent::Offset {
            base: Rc::new(acc),
            offset: i,
        });

    (field_ident, field_ty, field_degree)
}

fn is_ptr_type(ty: TypeRef) -> bool {
    matches!(ty.as_ref(), Type::PointerType { .. })
}

fn is_struct_type(ty: TypeRef) -> bool {
    matches!(
        ty.as_ref(),
        Type::StructType { .. } | Type::NamedStructType { .. }
    )
}
