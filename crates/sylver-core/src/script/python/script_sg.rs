use std::cell::RefCell;

use rustpython_vm::builtins::PyList;
use rustpython_vm::{
    builtins::PyStr, convert::ToPyObject, function::FuncArgs, pyclass, PyObjectRef, PyPayload,
    PyResult, VirtualMachine,
};

use crate::{
    script::ScriptEvalCtx,
    semantic::names::{SGraph, ScopeId},
};

use super::script_node::ScriptNode;

#[pyclass(name = "ScriptSG", module = "sylver")]
#[derive(Debug, PyPayload)]
pub struct ScriptSG {
    scope_graph: RefCell<SGraph>,
    scope: ScopeId,
    ctx: RefCell<ScriptEvalCtx>,
}

impl ScriptSG {
    pub fn new(ctx: RefCell<ScriptEvalCtx>, scope_graph: RefCell<SGraph>, scope: ScopeId) -> Self {
        Self {
            ctx,
            scope_graph,
            scope,
        }
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
        Ok(ScriptSG::new(self.ctx.clone(), self.scope_graph.clone(), scope).to_pyobject(vm))
    }

    #[pymethod]
    fn lookup(&self, args: FuncArgs, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        let name = get_arg(&args, 0, vm)?
            .payload::<PyStr>()
            .ok_or_else(|| vm.new_value_error("expected name to be a string".to_owned()))?;

        let nodes = self
            .scope_graph
            .borrow()
            .lookup(self.scope, name.to_string().as_str())
            .into_iter()
            .map(|n| ScriptNode::new(self.ctx.clone(), n));

        let list = PyList::default();
        for node in nodes {
            list.borrow_vec_mut().push(node.to_pyobject(vm));
        }

        Ok(list.to_pyobject(vm))
    }
}

fn get_arg<'a>(args: &'a FuncArgs, pos: usize, vm: &VirtualMachine) -> PyResult<&'a PyObjectRef> {
    args.args
        .get(pos)
        .ok_or_else(|| vm.new_value_error(format!("expected argument at pos {}", pos)))
}
