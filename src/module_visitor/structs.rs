use std::ops::Deref;
use std::rc::Rc;

use hashbrown::HashMap;
use llvm_ir::{Module, Type, TypeRef};

use super::{get_struct_from_name, strip_array_types};

pub type StructMap<'a> = HashMap<&'a String, Rc<StructType>>;

#[derive(Clone, Debug)]
pub struct StructField {
    pub st: Rc<StructType>,
    pub degree: usize,
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
    pub fn add_to_structs<'a>(
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

pub fn count_flattened_fields(struct_type: &StructType) -> usize {
    let mut num_sub_cells = 0;

    for field in &struct_type.fields {
        num_sub_cells += match field {
            Some(f) => count_flattened_fields(f),
            None => 1,
        };
    }

    num_sub_cells
}

pub fn get_struct_type<'a>(ty: &'a TypeRef, structs: &StructMap) -> Option<Rc<StructType>> {
    let (stripped_ty, _) = strip_array_types(ty);
    match stripped_ty.as_ref() {
        Type::NamedStructType { name } => structs.get(name).cloned(),
        _ => None,
    }
}
