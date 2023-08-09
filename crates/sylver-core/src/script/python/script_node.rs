use crate::query::{
    expr::{EvalCtx, Value},
    RawTreeInfoBuilder, SylvaNode,
};

use rustpython_vm::{
    builtins::{PyList, PyStrRef},
    convert::ToPyObject,
    pyclass, PyObject, PyObjectRef, PyPayload, PyResult, VirtualMachine,
};

#[pyclass(name = "ScriptNode", module = "sylver")]
#[derive(Debug, PyPayload)]
pub struct ScriptNode {
    // This will, in general, not be a reference to an actual 'static value.
    // A transmutation is done to hide the lifetime from the Python interpreter.
    // As a result, `ScriptNode` values should always be short-lived.
    ctx: *mut EvalCtx<'static, RawTreeInfoBuilder<'static>>,
    pub node: SylvaNode,
}

impl ScriptNode {
    pub fn new<'c>(ctx: &mut EvalCtx<'c, RawTreeInfoBuilder<'c>>, node: SylvaNode) -> Self {
        Self {
            ctx: unsafe { std::mem::transmute(ctx) },
            node,
        }
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
        let ctx = unsafe { &mut *self.ctx };
        ctx.node_text(self.node).to_pyobject(vm)
    }

    fn node_children(&self, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        let ctx = unsafe { &mut *self.ctx };
        let list = PyList::default();

        for c in ctx.childs(self.node) {
            let child = ScriptNode {
                ctx: self.ctx,
                node: c,
            };
            list.borrow_vec_mut().push(child.to_pyobject(vm));
        }

        Ok(list.to_pyobject(vm))
    }

    fn node_field(&self, field_name: &str, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        let ctx = unsafe { &mut *self.ctx };
        match ctx.node_field(self.node, field_name) {
            Ok(Value::Null) => Ok(vm.ctx.none()),
            Ok(Value::Node(n)) => Ok(ScriptNode {
                node: n,
                ctx: self.ctx,
            }
            .to_pyobject(vm)),
            _ => Err(vm.new_exception_msg(
                vm.ctx.exceptions.key_error.to_owned(),
                format!("Missing attribute: {field_name}"),
            )),
        }
    }
}
