use std::rc::Rc;

use hashbrown::HashMap;
use llvm_ir::{Module, Type, TypeRef};

use super::{get_struct_from_name, strip_array_types};

pub type StructMap = HashMap<String, Rc<StructType>>;

#[derive(Clone, Debug)]
pub struct StructField {
    pub st: Option<Rc<StructType>>,
    pub ty: TypeRef,
    pub degree: usize,
}

#[derive(Clone, Debug)]
pub struct StructType {
    pub fields: Vec<StructField>,
    pub size: usize,
}

impl StructType {
    pub fn from_fields(fields: &[TypeRef], structs: &mut StructMap, module: &Module) -> Rc<Self> {
        let mut size = 0;
        let fields = fields
            .iter()
            .map(|f| {
                let (ty, degree) = strip_array_types(f.clone());
                let st = match ty.as_ref() {
                    Type::NamedStructType { name } => {
                        let st = Self::lookup_or_new(name, structs, module);
                        size += st.size;
                        Some(st)
                    }
                    Type::StructType { element_types, .. } => {
                        let st = Self::from_fields(element_types, structs, module);
                        size += st.size;
                        Some(st)
                    }
                    _ => {
                        size += 1;
                        None
                    }
                };
                StructField {
                    st,
                    ty: ty.clone(),
                    degree,
                }
            })
            .collect();
        Rc::new(Self { fields, size })
    }

    pub fn try_from_type(ty: TypeRef, structs: &StructMap) -> Option<Rc<Self>> {
        Self::try_from_type_with_degree(ty, structs).map(|(st, _)| st)
    }

    pub fn try_from_type_with_degree(
        ty: TypeRef,
        structs: &StructMap,
    ) -> Option<(Rc<Self>, usize)> {
        let (stripped_ty, degree) = strip_array_types(ty);
        match stripped_ty.as_ref() {
            Type::NamedStructType { name } => structs.get(name).cloned().map(|s| (s, degree)),
            Type::StructType { element_types, .. } => {
                let mut size = 0;
                let fields = element_types
                    .iter()
                    .cloned()
                    .map(|f| {
                        let (ty, degree) = strip_array_types(f);
                        let st = Self::try_from_type(ty.clone(), structs);
                        match &st {
                            Some(st) => size += st.size,
                            None => size += 1,
                        }
                        StructField { st, ty, degree }
                    })
                    .collect();
                Some((Rc::new(Self { fields, size }), degree))
            }
            _ => None,
        }
    }

    pub fn add_to_structs(name: &String, ty: TypeRef, structs: &mut StructMap, module: &Module) {
        let fields = match ty.as_ref() {
            Type::StructType { element_types, .. } => element_types,
            _ => panic!("ty should only be a StructType"),
        };

        let struct_type = Self::from_fields(fields, structs, module);
        structs.insert(name.clone(), struct_type);
    }

    fn lookup_or_new<'a>(name: &String, structs: &mut StructMap, module: &'a Module) -> Rc<Self> {
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
