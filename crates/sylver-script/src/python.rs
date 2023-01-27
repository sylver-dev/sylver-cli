use std::collections::BTreeMap;

use rustpython_parser::ast;
use rustpython_vm::{
    builtins::{PyBaseExceptionRef, PyDict, PyInt, PyList, PyStr},
    bytecode::CodeObject,
    convert::ToPyObject,
    AsObject, Interpreter, PyObjectRef, PyRef, VirtualMachine,
};

use crate::{ScriptEngine, ScriptError, ScriptValue};

#[derive(Debug, Clone)]
pub struct PythonScript {
    invokable: PyObjectRef,
}

pub struct PythonScriptCompiler<'i> {
    interpreter: &'i Interpreter,
}

impl<'i> PythonScriptCompiler<'i> {
    pub fn new(interpreter: &'i Interpreter) -> Self {
        Self { interpreter }
    }

    pub fn compile_function(
        &self,
        code: &str,
        path: &str,
        fn_name: &str,
    ) -> Result<PythonScript, ScriptError> {
        let mut ast = Self::parse_module(code, path)?;
        Self::append_func_ref(path, fn_name, &mut ast)?;

        let invokable = self.run_code_obj(Self::compile_ast(path, &mut ast)?)?;

        Ok(PythonScript { invokable })
    }

    fn run_code_obj(&self, module_obj: CodeObject) -> Result<PyObjectRef, ScriptError> {
        self.interpreter.enter(|vm| {
            let module_code = vm.ctx.new_code(module_obj);
            vm.run_code_obj(module_code, vm.new_scope_with_builtins())
                .map_err(|e| to_script_error(vm, e))
        })
    }

    fn compile_ast(path: &str, ast: &mut ast::Mod) -> Result<CodeObject, ScriptError> {
        rustpython_codegen::compile::compile_top(
            ast,
            path.to_string(),
            rustpython_vm::compiler::Mode::BlockExpr,
            rustpython_codegen::CompileOpts { optimize: 1 },
        )
        .map_err(|e| ScriptError::Compilation(path.to_string(), e.to_string()))
    }

    /// Given the AST of a module defining a top-level `fn_name` function, append a reference to
    /// that function at the end of the module's body (so that evaluating the module as a block
    /// expression returns a reference to the given function).
    fn append_func_ref(path: &str, fn_name: &str, ast: &mut ast::Mod) -> Result<(), ScriptError> {
        let ast::Mod::Interactive { ref mut body , ..} = ast else {
            return Err(ScriptError::Compilation(path.to_string(), "Not a module".to_string()));
        };

        if !body.iter().any(
            |stmt| matches!(&stmt.node, ast::StmtKind::FunctionDef { name, ..} if name == fn_name),
        ) {
            return Err(ScriptError::Compilation(
                path.to_string(),
                format!("Function {fn_name} not found"),
            ));
        };

        let Some(last_statement) = body.last() else {
            return Err(ScriptError::Compilation(
                path.to_string(),
                "Empty script".to_string(),
            ));
        };

        let end_pos = last_statement
            .end_location
            .unwrap_or(last_statement.location);

        body.push(Self::build_name_stmt(end_pos, fn_name));

        Ok(())
    }

    fn build_name_stmt(location: ast::Location, name: &str) -> ast::Located<ast::StmtKind> {
        ast::Located::new(
            location,
            location,
            ast::StmtKind::Expr {
                value: Box::new(ast::Located::new(
                    location,
                    location,
                    ast::ExprKind::Name {
                        id: name.to_string(),
                        ctx: ast::ExprContext::Load,
                    },
                )),
            },
        )
    }

    fn parse_module(code: &str, path: &str) -> Result<ast::Mod, ScriptError> {
        rustpython_parser::parser::parse(code, rustpython_parser::parser::Mode::Interactive, path)
            .map_err(|e| ScriptError::Compilation(path.to_string(), e.to_string()))
    }
}

fn to_script_error(vm: &VirtualMachine, err: PyBaseExceptionRef) -> ScriptError {
    let mut msg = String::new();
    vm.write_exception(&mut msg, &err).unwrap();
    ScriptError::RuntimeError(msg)
}

pub struct PythonScriptEngine {
    interpreter: Interpreter,
}

impl ScriptEngine for PythonScriptEngine {
    type Script = PythonScript;

    fn eval(
        &self,
        script: &Self::Script,
        args: Vec<ScriptValue>,
    ) -> Result<ScriptValue, ScriptError> {
        let value = self.interpreter.enter(|vm| {
            let args: Vec<PyObjectRef> = args.into_iter().map(|arg| arg.to_pyobject(vm)).collect();
            vm.invoke(&script.invokable, args)
                .map_err(|e| to_script_error(vm, e))
        })?;

        value.try_into()
    }

    fn compile_function(
        &self,
        script: &str,
        file_name: &str,
        fun_name: &str,
    ) -> Result<Self::Script, ScriptError> {
        PythonScriptCompiler::new(&self.interpreter).compile_function(script, file_name, fun_name)
    }
}

impl Default for PythonScriptEngine {
    fn default() -> Self {
        Self {
            interpreter: Interpreter::with_init(Default::default(), |vm| {
                vm.add_frozen(rustpython_pylib::frozen_stdlib());
                vm.add_native_modules(rustpython_vm::stdlib::get_module_inits());
            }),
        }
    }
}

impl ToPyObject for ScriptValue {
    fn to_pyobject(self, vm: &VirtualMachine) -> PyObjectRef {
        match self {
            ScriptValue::Integer(i) => i.to_pyobject(vm),
            ScriptValue::Bool(b) => b.to_pyobject(vm),
            ScriptValue::Str(s) => s.to_pyobject(vm),
            ScriptValue::List(l) => {
                let list = PyList::default();
                for item in l {
                    list.borrow_vec_mut().push(item.to_pyobject(vm));
                }
                list.to_pyobject(vm)
            }
            ScriptValue::Dict(d) => {
                let dict = PyDict::default();
                for (k, v) in d {
                    dict.get_or_insert(vm, k.to_pyobject(vm), || v.to_pyobject(vm))
                        .expect("Conversion to PyObject failed");
                }
                dict.to_pyobject(vm)
            }
        }
    }
}

impl TryInto<ScriptValue> for PyObjectRef {
    type Error = ScriptError;

    fn try_into(self) -> Result<ScriptValue, Self::Error> {
        let value = if self.class().name().to_string() == "bool" {
            pybool_to_value(self.payload::<PyInt>().unwrap())
        } else if let Some(pyint) = self.payload::<PyInt>() {
            pyint_to_value(pyint)?
        } else if let Some(pystr) = self.payload::<PyStr>() {
            pystr_to_value(pystr)
        } else if let Ok(pydict) = self.clone().downcast::<PyDict>() {
            pydict_to_value(pydict)?
        } else if let Some(pylist) = self.payload::<PyList>() {
            pylist_to_value(pylist)?
        } else {
            return Err(ScriptError::UnsupportedType(
                self.class().name().to_string(),
            ));
        };

        Ok(value)
    }
}

fn pyint_to_value(pyint: &PyInt) -> Result<ScriptValue, ScriptError> {
    let int_value = i64::try_from(pyint.as_bigint())
        .map_err(|_| ScriptError::UnsupportedType("big_int".to_string()))?;

    Ok(ScriptValue::Integer(int_value))
}

fn pybool_to_value(pyint: &PyInt) -> ScriptValue {
    let bool_value = pyint_to_value(pyint).unwrap() == ScriptValue::Integer(1);
    ScriptValue::Bool(bool_value)
}

fn pystr_to_value(pystr: &PyStr) -> ScriptValue {
    ScriptValue::Str(pystr.to_string())
}

fn pylist_to_value(pylist: &PyList) -> Result<ScriptValue, ScriptError> {
    let values = pylist
        .borrow_vec()
        .iter()
        .map(|item| item.clone().try_into())
        .collect::<Result<_, ScriptError>>()?;

    Ok(ScriptValue::List(values))
}

fn pydict_to_value(pydict: PyRef<PyDict>) -> Result<ScriptValue, ScriptError> {
    let mut map = BTreeMap::new();

    for (key_value, value) in pydict {
        let key: &PyStr = key_value.payload::<PyStr>().ok_or_else(|| {
            ScriptError::UnsupportedType(format!("DictKey({})", key_value.class()))
        })?;

        let value = value.try_into()?;

        map.insert(key.to_string(), value);
    }

    Ok(ScriptValue::Dict(map))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn script_from_fun() {
        let python_module = r#"
def value():
    return 42

def hello(n: int):
    return value() + n
"#;

        let interpreter = Interpreter::without_stdlib(Default::default());
        let compiler = PythonScriptCompiler::new(&interpreter);

        let script = compiler
            .compile_function(python_module, "test.py", "hello")
            .unwrap();

        let engine = PythonScriptEngine { interpreter };

        let value = engine
            .eval(&script, vec![ScriptValue::Integer(10)])
            .unwrap();

        assert_eq!(value, ScriptValue::Integer(52));
    }

    #[test]
    fn python_int_to_int() {
        assert_eq!(ScriptValue::Integer(42), eval_python_expr("42"));
    }

    #[test]
    fn python_true_to_bool() {
        assert_eq!(ScriptValue::Bool(true), eval_python_expr("True"));
    }

    #[test]
    fn python_false_to_bool() {
        assert_eq!(ScriptValue::Bool(false), eval_python_expr("False"));
    }

    #[test]
    fn python_str_to_str() {
        assert_eq!(
            ScriptValue::Str("hello".to_string()),
            eval_python_expr("'hello'")
        );
    }

    #[test]
    fn python_list_to_list() {
        assert_eq!(
            ScriptValue::List(vec![
                ScriptValue::Integer(1),
                ScriptValue::Str("hello".to_string())
            ]),
            eval_python_expr("[1, 'hello']")
        )
    }

    #[test]
    fn python_dict_to_dict() {
        let expected = ScriptValue::Dict(
            vec![
                ("a".to_string(), ScriptValue::Integer(1)),
                ("b".to_string(), ScriptValue::Str("hello".to_string())),
                (
                    "c".to_string(),
                    ScriptValue::Dict(
                        vec![("d".to_string(), ScriptValue::Integer(2))]
                            .into_iter()
                            .collect(),
                    ),
                ),
            ]
            .into_iter()
            .collect(),
        );

        assert_eq!(
            expected,
            eval_python_expr("{'a': 1, 'b': 'hello', 'c': {'d': 2}}")
        );
    }

    fn eval_python_expr(expr: &str) -> ScriptValue {
        Interpreter::without_stdlib(Default::default())
            .enter(|vm| vm.run_block_expr(vm.new_scope_with_builtins(), expr))
            .unwrap()
            .try_into()
            .unwrap()
    }
}
