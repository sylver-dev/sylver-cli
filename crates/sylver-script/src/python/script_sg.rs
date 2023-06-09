use std::{cell::RefCell, rc::Rc};

use rustpython_vm::{
    builtins::PyStr, convert::ToPyObject, function::FuncArgs, pyclass, PyObjectRef, PyPayload,
    PyResult, VirtualMachine,
};

use sylver_core::semantic::names::{SGraph, ScopeId};

use crate::python::script_node::ScriptNode;

#[pyclass(name = "ScriptSG", module = "sylver")]
#[derive(Debug, PyPayload)]
pub struct ScriptSG {
    scope_graph: Rc<RefCell<SGraph>>,
    scope: ScopeId,
}

impl ScriptSG {
    fn new(scope_graph: Rc<RefCell<SGraph>>, scope: ScopeId) -> Self {
        Self { scope_graph, scope }
    }
}

#[pyclass]
impl ScriptSG {
    #[pymethod]
    fn add_decl(&self, args: FuncArgs, vm: &VirtualMachine) -> PyResult<()> {
        let name = get_arg(&args, 0, vm)?
            .payload::<PyStr>()
            .ok_or_else(|| vm.new_value_error("expected name to be a string".to_owned()))?;

        let node = get_arg(&args, 1, vm)?
            .payload::<ScriptNode>()
            .ok_or_else(|| vm.new_value_error("expected node to be a ScriptNode".to_owned()))?;

        let mut scope_graph = self.scope_graph.borrow_mut();
        scope_graph.add_decl(self.scope, name.to_string(), node.node);

        Ok(())
    }

    #[pymethod]
    fn add_scope(&self, _args: FuncArgs, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        let mut scope_graph = self.scope_graph.borrow_mut();
        let scope = scope_graph.add_scope(self.scope);
        Ok(ScriptSG::new(self.scope_graph.clone(), scope).to_pyobject(vm))
    }
}

fn get_arg<'a>(args: &'a FuncArgs, pos: usize, vm: &VirtualMachine) -> PyResult<&'a PyObjectRef> {
    args.args
        .get(pos)
        .ok_or_else(|| vm.new_value_error(format!("expected argument at pos {}", pos)))
}
