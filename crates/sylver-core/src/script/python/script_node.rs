use std::cell::RefCell;

use rustpython_vm::{
    builtins::{PyList, PyStrRef},
    convert::ToPyObject,
    pyclass, PyObject, PyObjectRef, PyPayload, PyResult, VirtualMachine,
};

use crate::{
    query::{expr::Value, SylvaNode},
    script::ScriptEvalCtx,
};

#[pyclass(name = "ScriptNode", module = "sylver")]
#[derive(Debug, PyPayload)]
pub struct ScriptNode {
    ctx: RefCell<ScriptEvalCtx>,
    pub node: SylvaNode,
}

impl ScriptNode {
    pub fn new(ctx: RefCell<ScriptEvalCtx>, node: SylvaNode) -> Self {
        Self { ctx, node }
    }
}

unsafe impl Send for ScriptNode {}

#[pyclass]
impl ScriptNode {
    #[pyslot]
    fn getattro(obj: &PyObject, name: PyStrRef, vm: &VirtualMachine) -> PyResult {
        if let Some(script_node) = obj.payload::<ScriptNode>() {
            match name.as_str() {
                "children" => ScriptNode::node_children(script_node, vm),
                "text" => Ok(script_node.text(vm)),
                field_name => ScriptNode::node_field(script_node, field_name, vm),
            }
        } else {
            Err(vm.new_type_error("Expected ScriptNode".to_owned()))
        }
    }

    fn text(&self, vm: &VirtualMachine) -> PyObjectRef {
        self.ctx
            .borrow_mut()
            .ctx_mut()
            .node_text(self.node)
            .to_pyobject(vm)
    }

    fn node_children(&self, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        let list = PyList::default();

        for c in self.ctx.borrow().ctx().childs(self.node) {
            let child = ScriptNode {
                ctx: self.ctx.clone(),
                node: c,
            };
            list.borrow_vec_mut().push(child.to_pyobject(vm));
        }

        Ok(list.to_pyobject(vm))
    }

    fn node_field(&self, field_name: &str, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        match self.ctx.borrow().ctx().node_field(self.node, field_name) {
            Ok(Value::Null) => Ok(vm.ctx.none()),
            Ok(Value::Node(n)) => Ok(ScriptNode {
                node: n,
                ctx: self.ctx.clone(),
            }
            .to_pyobject(vm)),
            _ => Err(vm.new_exception_msg(
                vm.ctx.exceptions.key_error.to_owned(),
                format!("Missing attribute: {field_name}"),
            )),
        }
    }
}
