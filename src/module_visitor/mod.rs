use std::fmt::{self, Display, Formatter};
use std::rc::Rc;
use std::str::FromStr;

use hashbrown::HashMap;
use llvm_ir::function::FunctionDeclaration;
use llvm_ir::module::GlobalVariable;
use llvm_ir::types::NamedStructDef;
use llvm_ir::{Function, Instruction, Module, Name, Terminator, Type, TypeRef};

use self::structs::{StructMap, StructType};

pub mod pointer;
pub mod std_functions;
pub mod structs;

#[derive(Clone, Copy)]
pub struct Context<'a, 'b> {
    pub module: &'a Module,
    pub function: Option<&'a Function>,
    pub structs: &'b StructMap,
}

/// This trait allows implementors to define handler functions for llvm constructs,
/// which the `visit_module` function will call.
pub trait ModuleVisitor<'a> {
    fn init(&mut self, context: Context<'a, '_>);
    fn handle_function(&mut self, function: &'a Function, context: Context<'a, '_>);
    fn handle_fun_decl(&mut self, fun_decl: &'a FunctionDeclaration, context: Context<'a, '_>);
    fn handle_global(&mut self, global: &'a GlobalVariable, context: Context<'a, '_>);
    fn handle_instruction(&mut self, instr: &'a Instruction, context: Context<'a, '_>);
    fn handle_terminator(&mut self, term: &'a Terminator, context: Context<'a, '_>);
    fn finalize(&mut self, context: Context<'a, '_>);

    fn visit_module(&mut self, module: &'a Module) {
        let mut structs = HashMap::new();
        for (name, ty) in module
            .types
            .all_struct_names()
            .filter_map(|name| get_struct_from_name(name, module).map(|t| (name, t)))
        {
            StructType::add_to_structs(name, ty, &mut structs, module);
        }

        let context = Context {
            module,
            function: None,
            structs: &structs,
        };

        self.init(context);

        for global in &module.global_vars {
            self.handle_global(global, context);
        }

        for fun_decl in &module.func_declarations {
            self.handle_fun_decl(fun_decl, context);
        }

        for function in &module.functions {
            self.handle_function(function, context);
            for block in &function.basic_blocks {
                let context = Context {
                    function: Some(function),
                    ..context
                };

                for instr in &block.instrs {
                    self.handle_instruction(instr, context);
                }
                self.handle_terminator(&block.term, context)
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum VarIdent {
    Local {
        reg_name: Rc<Name>,
        fun_name: Rc<str>,
    },
    Global {
        name: Rc<str>,
    },
    Fresh {
        index: usize,
    },
    Offset {
        base: Rc<Self>,
        offset: usize,
    },
}

impl VarIdent {
    pub fn new_local(reg_name: &Name, fun_name: &str) -> Self {
        Self::Local {
            reg_name: Rc::new(reg_name.clone()),
            fun_name: fun_name.into(),
        }
    }
    pub fn new_global(name: &str) -> Self {
        Self::Global { name: name.into() }
    }
}

// impl<'a> ToOwned for VarIdent<'a> {
//     type Owned = OwnedVarIdent;

//     fn to_owned(&self) -> Self::Owned {
//         match self {
//             Self::Local { reg_name, fun_name } => write!(f, "{reg_name}@{fun_name}"),
//             Self::Global { name } => write!(f, "{name}"),
//             Self::Fresh { index } => write!(f, "fresh_{index}"),
//             Self::Offset { base, offset } => write!(f, "{base}[{offset}]"),
//         }
//     }
// }

impl Display for VarIdent {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Local { reg_name, fun_name } => write!(f, "{reg_name}@{fun_name}"),
            Self::Global { name } => write!(f, "{name}"),
            Self::Fresh { index } => write!(f, "fresh_{index}"),
            Self::Offset { base, offset } => write!(f, "{base}[{offset}]"),
        }
    }
}

impl FromStr for VarIdent {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // offset case
        if let Some((l, r)) = s.rsplit_once('[') {
            if r.chars().last() == Some(']') {
                let offset = r[..r.len() - 1]
                    .parse()
                    .map_err(|_| String::from("Offset was not a number"))?;
                return Ok(VarIdent::Offset {
                    base: Rc::new(l.parse()?),
                    offset,
                });
            } else {
                return Err(format!("Missing closing bracket in '{s}'"));
            }
        }
        // fresh case
        if s.starts_with("fresh_") {
            let index = s["fresh_".len()..]
                .parse()
                .map_err(|_| String::from("Could not parse fresh index"))?;
            return Ok(VarIdent::Fresh { index });
        }
        if s.len() == 0 || !s.starts_with('%') {
            Err(format!("Could not parse ident '{s}'"))
        } else {
            let s: &str = &s[1..];
            if let Some((reg_name, fun_name)) = s.rsplit_once('@') {
                let name = match reg_name.parse() {
                    Ok(index) => Name::Number(index),
                    Err(_) => Name::Name(Box::new(reg_name.to_owned())),
                };
                Ok(VarIdent::Local {
                    reg_name: Rc::new(name),
                    fun_name: fun_name.to_owned().into(),
                })
            } else {
                Ok(VarIdent::Global {
                    name: s.to_owned().into(),
                })
            }
        }
    }
}

fn strip_array_types(ty: TypeRef) -> (TypeRef, usize) {
    match ty.as_ref() {
        Type::ArrayType { element_type, .. } | Type::VectorType { element_type, .. } => {
            let (ty, degree) = strip_array_types(element_type.clone());
            (ty, degree + 1)
        }
        _ => (ty, 0),
    }
}

fn strip_pointer_type(ty: TypeRef) -> Option<TypeRef> {
    match ty.as_ref() {
        Type::PointerType { pointee_type, .. } => Some(pointee_type.clone()),
        _ => None,
    }
}

fn get_struct_from_name(name: &str, Module { types, .. }: &Module) -> Option<TypeRef> {
    types.named_struct_def(name).and_then(|def| match def {
        NamedStructDef::Opaque => None,
        NamedStructDef::Defined(ty) => Some(ty.clone()),
    })
}
