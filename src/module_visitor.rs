use llvm_ir::{BasicBlock, Function, Instruction, Module, Terminator};

#[derive(Clone, Copy)]
pub struct Context<'a> {
    pub module: &'a Module,
    pub function: &'a Function,
    pub block: &'a BasicBlock,
}

/// This trait allows implementors to define the `handle_instruction` and `handle_terminator` functions,
/// which the `visit_module` function will call on all instructions and terminators.
pub trait ModuleVisitor {
    fn handle_instruction(&mut self, instr: &Instruction, context: Context);
    fn handle_terminator(&mut self, term: &Terminator, context: Context);

    fn visit_module(&mut self, module: &Module) {
        for function in &module.functions {
            for block in &function.basic_blocks {
                let context = Context {
                    module,
                    function,
                    block,
                };

                for instr in &block.instrs {
                    self.handle_instruction(instr, context);
                }
                self.handle_terminator(&block.term, context)
            }
        }
    }
}
