use std::cell::RefCell;

use rustpython_vm::{
    builtins::{PyList, PyStr},
    convert::ToPyObject,
    pyclass, Py, PyObject, PyObjectRef, PyPayload, PyResult, VirtualMachine,
};

use crate::{query::SylvaNode, script::ScriptTreeInfo, tree::info::TreeInfo};

#[pyclass(name = "ScriptNode", module = "sylver")]
#[derive(Debug, PyPayload)]
pub struct ScriptNode {
    info: RefCell<ScriptTreeInfo>,
    pub node: SylvaNode,
}

impl ScriptNode {
    pub fn new(info: RefCell<ScriptTreeInfo>, node: SylvaNode) -> Self {
        Self { info, node }
    }
}

unsafe impl Send for ScriptNode {}

#[pyclass]
impl ScriptNode {
    #[pyslot]
    fn getattro(obj: &PyObject, name: &Py<PyStr>, vm: &VirtualMachine) -> PyResult {
        if let Some(script_node) = obj.payload::<ScriptNode>() {
            match name.as_str() {
                "children" => ScriptNode::node_children(script_node, vm),
                "kind" => Ok(ScriptNode::kind(script_node, vm)),
                "text" => Ok(script_node.text(vm)),
                field_name => ScriptNode::node_field(script_node, field_name, vm),
            }
        } else {
            Err(vm.new_type_error("Expected ScriptNode".to_owned()))
        }
    }

    fn text(&self, vm: &VirtualMachine) -> PyObjectRef {
        self.info
            .borrow_mut()
            .info_mut()
            .node_text(self.node.node)
            .to_pyobject(vm)
    }

    fn kind(&self, vm: &VirtualMachine) -> PyObjectRef {
        self.info
            .borrow()
            .info()
            .proxy(self.node.node)
            .kind_name()
            .to_pyobject(vm)
    }

    fn node_children(&self, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        let list = PyList::default();

        for c in self
            .info
            .borrow()
            .info()
            .proxy(self.node.node)
            .direct_children()
        {
            let child = ScriptNode {
                info: self.info.clone(),
                node: self.node.with_node_id(c.id),
            };
            list.borrow_vec_mut().push(child.to_pyobject(vm));
        }

        Ok(list.to_pyobject(vm))
    }

    fn node_field(&self, field_name: &str, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        match self
            .info
            .borrow()
            .info()
            .field_value_from_name(self.node.node, field_name)
        {
            Some(n) => Ok(ScriptNode {
                node: self.node.with_node_id(n),
                info: self.info.clone(),
            }
            .to_pyobject(vm)),
            None => Err(vm.new_exception_msg(
                vm.ctx.exceptions.key_error.to_owned(),
                format!("Missing attribute: {field_name}"),
            )),
        }
    }
}
