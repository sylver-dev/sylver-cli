use rustpython_vm::pymodule;

#[pymodule]
pub mod path {
    use std::path::Path;

    use rustpython_vm::{PyObjectRef, PyResult, VirtualMachine};

    #[pyfunction]
    fn isdir(path: String, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        Ok(vm.new_pyobj(Path::new(&path).is_dir()))
    }

    #[pyfunction]
    fn relpath(path: String, start: String, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        Path::new(&path)
            .strip_prefix(&start)
            .map(|stripped| vm.new_pyobj(stripped.to_string_lossy().to_string()))
            .map_err(|e| vm.new_value_error(format!("Could not strip prefix: {e}")))
    }

    #[pyfunction]
    fn join(path: String, suffix: String, vm: &VirtualMachine) -> PyObjectRef {
        let joined = Path::new(&path).join(suffix).to_string_lossy().to_string();
        vm.new_pyobj(joined)
    }
}

#[pymodule]
pub mod os {
    use std::path::Path;

    use rustpython_vm::{pyclass, PyObjectRef, PyPayload, PyResult, VirtualMachine};

    #[pyfunction]
    fn listdir(path: String, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        let Ok(entries) = std::fs::read_dir(&path) else {
            return Err(vm.new_value_error(format!("Could not read directory: {path}")));
        };

        let file_names = entries
            .into_iter()
            .map(|entry| {
                let val = entry?.file_name().to_string_lossy().to_string();
                Ok(vm.new_pyobj(val))
            })
            .collect::<std::io::Result<Vec<PyObjectRef>>>()
            .map_err(|e| vm.new_value_error(format!("Could not read directory: {e}")))?;

        Ok(vm.new_pyobj(file_names))
    }
}

#[pymodule]
pub mod re {
    use rustpython_vm::{pyclass, PyObjectRef, PyPayload, PyResult, VirtualMachine};

    #[pyattr]
    #[pyclass(module = "re", name = "Regex")]
    #[derive(Debug, PyPayload)]
    struct Regex {
        regex: fancy_regex::Regex,
    }

    #[pyclass]
    impl Regex {
        #[pymethod(name = "match")]
        fn _match(&self, text: String, vm: &VirtualMachine) -> PyObjectRef {
            let is_match = matches!(self.regex.find(&text), Ok(Some(_)));
            vm.new_pyobj(is_match)
        }
    }

    #[pyfunction]
    fn compile(text: String, vm: &VirtualMachine) -> PyResult<Regex> {
        let Ok(regex) = fancy_regex::Regex::new(&text) else {
            return Err(vm.new_value_error(format!("Could not compile regex: {text}")));
        };

        Ok(Regex { regex })
    }
}

#[pymodule]
pub mod yaml {
    use rustpython_vm::{convert::ToPyObject, PyObjectRef, PyResult, VirtualMachine};
    use serde_yaml::Value;

    #[pyfunction]
    fn load(path: String, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        let Ok(doc) = std::fs::read_to_string(&path) else {
            return Err(vm.new_value_error(format!("Could not read file: {path}")));
        };

        loads(doc, vm)
    }

    #[pyfunction]
    fn loads(yaml_doc: String, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
        let Ok(value) = serde_yaml::from_str::<serde_yaml::Value>(&yaml_doc) else {
            return Err(vm.new_value_error("Invalid YAML document".to_string()));
        };

        yaml_value_to_pyref(vm, value)
    }

    fn yaml_value_to_pyref(vm: &VirtualMachine, value: Value) -> PyResult<PyObjectRef> {
        let python_value = match value {
            Value::Null | Value::Tagged(_) => vm.ctx.none(),
            Value::Bool(b) => vm.new_pyobj(b),
            Value::String(s) => vm.new_pyobj(s),
            Value::Sequence(s) => vm.new_pyobj(
                s.into_iter()
                    .map(|v| yaml_value_to_pyref(vm, v))
                    .collect::<PyResult<Vec<PyObjectRef>>>()?,
            ),
            Value::Mapping(m) => {
                let dict = vm.ctx.new_dict();
                for (k, v) in m {
                    dict.set_item(&to_string(vm, k)?, yaml_value_to_pyref(vm, v)?, vm)?
                }
                dict.to_pyobject(vm)
            }
            Value::Number(n) => {
                if let Some(i) = n.as_i64() {
                    vm.new_pyobj(i)
                } else if let Some(f) = n.as_f64() {
                    vm.new_pyobj(f)
                } else {
                    return Err(vm.new_value_error(format!("Invalid number: {n:?}")));
                }
            }
        };

        Ok(python_value)
    }

    fn to_string(vm: &VirtualMachine, value: Value) -> PyResult<String> {
        match value {
            Value::String(s) => Ok(s),
            _ => Err(vm.new_value_error(format!("Invalid dict key: {value:?}"))),
        }
    }
}
