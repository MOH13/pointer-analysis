use std::fmt::{self, Display, Formatter};

use hashbrown::HashMap;
use llvm_ir::module::GlobalVariable;
use llvm_ir::types::NamedStructDef;
use llvm_ir::{BasicBlock, Function, Instruction, Module, Name, Terminator, Type, TypeRef};

use self::structs::{StructMap, StructType};

pub mod pointer;
pub mod structs;

#[derive(Clone, Copy)]
pub struct Context<'a, 'b> {
    pub module: &'a Module,
    pub function: &'a Function,
    pub block: &'a BasicBlock,
    pub structs: &'b StructMap<'a>,
}

/// This trait allows implementors to define handler functions for llvm constructs,
/// which the `visit_module` function will call.
pub trait ModuleVisitor<'a> {
    fn handle_function(&mut self, function: &'a Function, module: &'a Module);
    fn handle_global(&mut self, global: &'a GlobalVariable, structs: &StructMap);
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
            self.handle_global(global, &structs);
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
    Fresh {
        index: usize,
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
            VarIdent::Fresh { index } => write!(f, "fresh_{index}"),
        }
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