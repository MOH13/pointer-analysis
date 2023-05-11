use crate::module_visitor::pointer::PointerModuleObserver;

pub struct DummyPointerObserver {
    counter: usize,
}

impl DummyPointerObserver {
    pub fn new() -> Self {
        DummyPointerObserver { counter: 0 }
    }

    pub fn get_counter(&self) -> usize {
        self.counter
    }
}

impl<'a> PointerModuleObserver<'a> for DummyPointerObserver {
    fn init(&mut self, _structs: &crate::module_visitor::structs::StructMap) {
        self.counter += 1;
    }

    fn handle_ptr_function(
        &mut self,
        _name: crate::module_visitor::VarIdent<'a>,
        _parameters: Vec<crate::module_visitor::VarIdent<'a>>,
        _return_struct_type: Option<std::rc::Rc<crate::module_visitor::structs::StructType>>,
    ) {
        self.counter += 1;
    }

    fn handle_ptr_global(
        &mut self,
        _ident: crate::module_visitor::VarIdent<'a>,
        _init_ref: Option<crate::module_visitor::VarIdent<'a>>,
        _struct_type: Option<std::rc::Rc<crate::module_visitor::structs::StructType>>,
    ) {
        self.counter += 1;
    }

    fn handle_ptr_instruction(
        &mut self,
        _instr: crate::module_visitor::pointer::PointerInstruction<'a>,
        _context: crate::module_visitor::pointer::PointerContext<'a>,
    ) {
        self.counter += 1;
    }
}
