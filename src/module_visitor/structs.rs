use std::rc::Rc;

use hashbrown::HashMap;
use llvm_ir::{Module, Type, TypeRef};

use super::{get_struct_from_name, strip_array_types};

pub type StructMap<'a> = HashMap<&'a String, Rc<StructType<'a>>>;

#[derive(Clone, Debug)]
pub struct StructField<'a> {
    pub st: Option<Rc<StructType<'a>>>,
    pub ty: &'a TypeRef,
    pub degree: usize,
}

#[derive(Clone, Debug)]
pub struct StructType<'a> {
    pub fields: Vec<StructField<'a>>,
}

impl<'a> StructType<'a> {
    pub fn add_to_structs(
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
                let st = match ty.as_ref() {
                    Type::NamedStructType { name } => {
                        Some(Self::lookup_or_new(name, structs, module))
                    }
                    _ => None,
                };
                StructField { st, ty, degree }
            })
            .collect();
        structs.insert(name, Rc::new(Self { fields }));
    }

    fn lookup_or_new(
        name: &'a String,
        structs: &mut StructMap<'a>,
        module: &'a Module,
    ) -> Rc<StructType<'a>> {
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

pub fn count_flattened_fields(struct_type: &StructType) -> usize {
    let mut num_sub_cells = 0;

    for field in &struct_type.fields {
        num_sub_cells += match &field.st {
            Some(st) => count_flattened_fields(st),
            None => 1,
        };
    }

    num_sub_cells
}

pub fn get_struct_type<'a>(
    ty: &'a TypeRef,
    structs: &StructMap<'a>,
) -> Option<(Rc<StructType<'a>>, usize)> {
    let (stripped_ty, degree) = strip_array_types(ty);
    match stripped_ty.as_ref() {
        Type::NamedStructType { name } => structs.get(name).cloned().map(|s| (s, degree)),
        _ => None,
    }
}
