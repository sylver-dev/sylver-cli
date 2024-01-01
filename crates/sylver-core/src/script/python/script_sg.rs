use std::cell::RefCell;
use std::sync::{Arc, RwLock};

use rustpython_vm::builtins::PyList;
use rustpython_vm::{
    builtins::PyStr, convert::ToPyObject, function::FuncArgs, pyclass, PyObjectRef, PyPayload,
    PyResult, VirtualMachine,
};

use crate::{
    script::ScriptTreeInfo,
    semantic::names::{SGraph, ScopeId},
};

use super::script_node::ScriptNode;

#[pyclass(name = "ScriptSG", module = "sylver")]
#[derive(Debug, PyPayload)]
pub struct ScriptSG {
    pub scope_graph: Arc<RwLock<SGraph>>,
    pub scope_id: ScopeId,
    pub ctx: RefCell<ScriptTreeInfo>,
}

impl ScriptSG {
    pub fn new(
        ctx: RefCell<ScriptTreeInfo>,
        scope_graph: Arc<RwLock<SGraph>>,
        scope_id: ScopeId,
    ) -> Self {
        Self {
            ctx,
            scope_graph,
            scope_id,
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

        let mut scope_graph = self.scope_graph.write().expect("poisoned scope graph lock");
        scope_graph.add_decl(self.scope_id, name.to_string(), node.node);

        Ok(())
    }

    #[pymethod]
    fn add_ref(&self, args: FuncArgs, vm: &VirtualMachine) -> PyResult<()> {
        let name = get_arg(&args, 0, vm)?
            .payload::<PyStr>()
            .ok_or_else(|| vm.new_value_error("expected name to be a string".to_owned()))?;

        let node = get_arg(&args, 1, vm)?
            .payload::<ScriptNode>()
            .ok_or_else(|| vm.new_value_error("expected node to be a ScriptNode".to_owned()))?;

        let mut scope_graph = self.scope_graph.write().expect("poisoned scope graph lock");
        scope_graph.add_ref(self.scope_id, name.to_string(), node.node);

        Ok(())
    }

    #[pymethod]
    fn add_scope(&self, _args: FuncArgs, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        let mut scope_graph = self.scope_graph.write().expect("poisoned scope graph lock");
        let scope = scope_graph.add_scope(self.scope_id);
        Ok(ScriptSG::new(self.ctx.clone(), self.scope_graph.clone(), scope).to_pyobject(vm))
    }

    #[pymethod]
    fn lookup(&self, args: FuncArgs, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        let name = get_arg(&args, 0, vm)?
            .payload::<PyStr>()
            .ok_or_else(|| vm.new_value_error("expected name to be a string".to_owned()))?;

        let nodes = self
            .scope_graph
            .read()
            .expect("poisoned scope graph lock")
            .lookup(self.scope_id, name.to_string().as_str())
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
