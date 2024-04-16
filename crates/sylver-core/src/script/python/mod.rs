use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap},
    ops::Deref,
    sync::{mpsc::Sender, Mutex, OnceLock},
};

use id_vec::{Id, IdVec};
use itertools::Itertools;
use rustpython_codegen::CompileOpts;
use rustpython_parser::ast::{
    self,
    located::{Expr, ExprAttribute, ExprName, Mod, Stmt},
    ExprCall, Fold, ModInteractive,
    Stmt::FunctionDef,
    StmtFunctionDef,
};
use rustpython_vm::{
    builtins::{PyBaseExceptionRef, PyDict, PyInt, PyList, PyStr},
    class::PyClassImpl,
    compiler::{self, LinearLocator},
    convert::ToPyObject,
    AsObject, Interpreter, PyObjectRef, PyRef, VirtualMachine,
};

use super::{ScriptEngine, ScriptError, ScriptQueryValue, ScriptTreeInfo, ScriptValue};

use script_node::ScriptNode;
use script_sg::ScriptSG;

mod script_node;
mod script_sg;
mod stdlib;

static PYTHON_CTX: OnceLock<Mutex<Sender<PythonMsg>>> = OnceLock::new();

struct PythonMsg {
    data: PythonMsgData,
    sender: Sender<PythonResp>,
}

enum PythonMsgData {
    Functions(Mod, String, Vec<String>),
    Script(PythonScript, Vec<ScriptValue>),
    ScriptInQuery(PythonScript, Vec<PythonScriptQueryArg>),
}

enum PythonScriptQueryArg {
    Value(ScriptValue),
    Node(ScriptNode),
}

#[derive(Debug, Clone)]
enum PythonResp {
    Scripts(HashMap<String, PythonScript>),
    Script(PythonScript),
    Value(ScriptValue),
    Error(ScriptError),
}

impl From<HashMap<String, PythonScript>> for PythonResp {
    fn from(scripts: HashMap<String, PythonScript>) -> Self {
        PythonResp::Scripts(scripts)
    }
}

impl From<ScriptValue> for PythonResp {
    fn from(value: ScriptValue) -> Self {
        PythonResp::Value(value)
    }
}

impl From<PythonScript> for PythonResp {
    fn from(invokable: PythonScript) -> Self {
        PythonResp::Script(invokable)
    }
}

impl<V: Into<PythonResp>> From<Result<V, ScriptError>> for PythonResp {
    fn from(result: Result<V, ScriptError>) -> Self {
        match result {
            Ok(value) => value.into(),
            Err(error) => PythonResp::Error(error),
        }
    }
}

impl TryInto<PythonScript> for PythonResp {
    type Error = ScriptError;

    fn try_into(self) -> Result<PythonScript, ScriptError> {
        match self {
            PythonResp::Script(script) => Ok(script),
            _ => Err(ScriptError::RuntimeError("script id".to_string())),
        }
    }
}

impl TryInto<ScriptValue> for PythonResp {
    type Error = ScriptError;

    fn try_into(self) -> Result<ScriptValue, ScriptError> {
        match self {
            PythonResp::Value(value) => Ok(value),
            val => Err(ScriptError::RuntimeError(format!(
                "expected script value, but got: {:?}",
                val
            ))),
        }
    }
}

impl TryInto<HashMap<String, PythonScript>> for PythonResp {
    type Error = ScriptError;

    fn try_into(self) -> Result<HashMap<String, PythonScript>, ScriptError> {
        match self {
            PythonResp::Scripts(scripts) => Ok(scripts),
            PythonResp::Error(err) => Err(ScriptError::RuntimeError(format!(
                "failed to build script collection: {}",
                err
            ))),
            _ => Err(ScriptError::RuntimeError(
                "expected script collection, but got: {:?}".to_string(),
            )),
        }
    }
}

pub struct PythonVM {
    interpreter: Interpreter,
    scripts: IdVec<PyObjectRef>,
}

impl PythonVM {
    fn functions(
        &mut self,
        ast: Mod,
        path: String,
        functions: Vec<String>,
    ) -> Result<HashMap<String, PythonScript>, ScriptError> {
        self.interpreter.enter(|vm| {
            let code = rustpython_codegen::compile::compile_top(
                &ast,
                path.to_string(),
                compiler::Mode::BlockExpr,
                CompileOpts { optimize: 1 },
            )
            .map_err(|e| ScriptError::Compilation(path.to_string(), e.to_string()))?;

            let code_obj = vm.ctx.new_code(code);

            let scope = vm.new_scope_with_builtins();
            let scope_copy = scope.clone();

            if let Err(e) = vm.run_code_obj(code_obj, scope) {
                return Err(to_script_error(vm, e));
            };

            functions
                .into_iter()
                .map(|name| {
                    let f = scope_copy.globals.get_item(&name, vm).map_err(|_| {
                        ScriptError::RuntimeError(format!("function {} not found", name))
                    })?;

                    let script = PythonScript {
                        invokable: self.scripts.insert(f).index_value(),
                    };

                    Ok((name, script))
                })
                .collect::<Result<HashMap<_, _>, _>>()
        })
    }

    fn run_script(
        &self,
        script: PythonScript,
        args: Vec<ScriptValue>,
    ) -> Result<ScriptValue, ScriptError> {
        let value = self.interpreter.enter(|vm| {
            let mut script_args = vec![];
            for a in args {
                script_args.push(a.to_pyobject(vm));
            }

            let invokable = self.scripts.get(Id::from_index(script.invokable)).ok_or(
                ScriptError::RuntimeError(format!("invalid script id: {}", script.invokable)),
            )?;

            invokable
                .call(script_args, vm)
                .map_err(|e| to_script_error(vm, e))
        })?;

        value.try_into()
    }

    fn run_script_in_query(
        &self,
        script: PythonScript,
        args: Vec<PythonScriptQueryArg>,
    ) -> Result<ScriptValue, ScriptError> {
        let value = self.interpreter.enter(|vm| {
            let mut script_args = vec![];
            for a in args {
                let script_arg = match a {
                    PythonScriptQueryArg::Value(val) => val.to_pyobject(vm),
                    PythonScriptQueryArg::Node(node) => node.to_pyobject(vm),
                };
                script_args.push(script_arg);
            }

            let invokable = self.scripts.get(Id::from_index(script.invokable)).ok_or(
                ScriptError::RuntimeError(format!("invalid script id: {}", script.invokable)),
            )?;

            invokable
                .call(script_args, vm)
                .map_err(|e| to_script_error(vm, e))
        })?;

        value.try_into()
    }
}

fn start_python_thread() -> Mutex<Sender<PythonMsg>> {
    let (sender, receiver) = std::sync::mpsc::channel::<PythonMsg>();

    std::thread::spawn(move || {
        let mut ctx = PythonVM {
            interpreter: interpreter_with_stdlib(),
            scripts: IdVec::new(),
        };

        for msg in receiver {
            let resp = match msg.data {
                PythonMsgData::Functions(ast, path, functions) => {
                    ctx.functions(ast, path, functions).into()
                }
                PythonMsgData::Script(script, args) => ctx.run_script(script, args).into(),
                PythonMsgData::ScriptInQuery(script, args) => {
                    ctx.run_script_in_query(script, args).into()
                }
            };

            msg.sender
                .send(resp)
                .expect("failed to send Python response");
        }
    });

    Mutex::new(sender)
}

fn send_python_msg_sync(msg: PythonMsgData) -> Result<PythonResp, ScriptError> {
    let (sender, receiver) = std::sync::mpsc::channel();

    PYTHON_CTX
        .get_or_init(start_python_thread)
        .lock()
        .map_err(|e| ScriptError::RuntimeError(format!("failed to lock Python runtime: {}", e)))?
        .send(PythonMsg { data: msg, sender })
        .map_err(|_| ScriptError::RuntimeError("failed to reach Python runtime".to_string()))?;

    receiver
        .recv()
        .map_err(|e| ScriptError::RuntimeError(format!("failed to receive Python response: {}", e)))
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct PythonScript {
    invokable: usize, // usize instead of id because it must be Send
}

pub fn compile_aspects(
    code: &str,
    path: String,
) -> Result<HashMap<String, HashMap<String, PythonScript>>, ScriptError> {
    let mut invokables: HashMap<String, HashMap<String, PythonScript>> = HashMap::new();

    let mut ast = parse_module(code, &path)?;

    let aspect_function_ids = collect_aspect_function_ids(&path, &mut ast)?;

    let aspect_funs = aspect_function_ids
        .values()
        .flatten()
        .map(|(_, f)| f.clone())
        .collect_vec();

    let aspect_scripts: HashMap<String, PythonScript> =
        send_python_msg_sync(PythonMsgData::Functions(ast, path.clone(), aspect_funs))?
            .try_into()?;

    for (aspect_name, aspect_impls) in aspect_function_ids {
        for (kind_name, impl_fn) in aspect_impls {
            invokables
                .entry(aspect_name.clone())
                .or_default()
                .insert(kind_name.clone(), aspect_scripts[&impl_fn]);
        }
    }

    Ok(invokables)
}

pub fn compile_function(
    code: &str,
    path: String,
    fn_name: String,
) -> Result<PythonScript, ScriptError> {
    let ast = parse_module(code, path.as_str())?;

    let invokable: HashMap<String, PythonScript> =
        send_python_msg_sync(PythonMsgData::Functions(ast, path, vec![fn_name.clone()]))?
            .try_into()?;

    Ok(invokable[&fn_name])
}

fn collect_aspect_function_ids(
    path: &str,
    ast: &mut Mod,
) -> Result<HashMap<String, Vec<(String, String)>>, ScriptError> {
    let ast::Mod::Interactive(ModInteractive { ref mut body, .. }) = ast else {
        return Err(ScriptError::Compilation(
            path.to_string(),
            "Not a module".to_string(),
        ));
    };

    let mut aspect_fns: HashMap<String, Vec<(String, String)>> = HashMap::new();

    for statement in body.iter_mut() {
        if let Some((aspect_name, kind_name, aspect_fn_name)) = extract_aspect_fn_ids(statement)? {
            aspect_fns
                .entry(aspect_name)
                .or_default()
                .push((kind_name, aspect_fn_name));
        }
    }

    Ok(aspect_fns)
}

fn parse_module(code: &str, path: &str) -> Result<Mod, ScriptError> {
    let ast = rustpython_parser::parse(code, rustpython_parser::Mode::Interactive, path)
        .map_err(|e| ScriptError::Compilation(path.to_string(), e.to_string()))?;

    let mut locator = LinearLocator::new(code);

    locator
        .fold_mod(ast)
        .map_err(|e| ScriptError::Compilation(path.to_string(), e.to_string()))
}

/// If the given statement is an aspect function definition, return a tuple
/// of the form (aspect_name, kind_name, function_name).
fn extract_aspect_fn_ids(
    statement: &mut Stmt,
) -> Result<Option<(String, String, String)>, ScriptError> {
    if let FunctionDef(StmtFunctionDef {
        name: function_name,
        decorator_list,
        ..
    }) = statement
    {
        if let Some((aspect_name, kind_name)) = find_aspect_target_kind_name(decorator_list)? {
            decorator_list.clear();
            return Ok(Some((aspect_name, kind_name, function_name.to_string())));
        }
    }

    Ok(None)
}

/// If the given decorator list is a valid aspect declaration,
/// return a tuple of the form (aspect_name, kind_name).
fn find_aspect_target_kind_name(
    decorator_list: &[Expr],
) -> Result<Option<(String, String)>, ScriptError> {
    match decorator_list {
        [] => Ok(None),
        [_, _, ..] => Err(ScriptError::InvalidAspectDeclaration),
        [decorator] => {
            if let Expr::Call(ExprCall { func, .. }) = &decorator {
                if let Expr::Attribute(ExprAttribute { value, attr, .. }) = func.deref() {
                    if let Expr::Name(ExprName { id: kind_name, .. }) = value.deref() {
                        return Ok(Some((attr.to_string(), kind_name.to_string())));
                    }
                }
            }
            Ok(None)
        }
    }
}

fn to_script_error(vm: &VirtualMachine, err: PyBaseExceptionRef) -> ScriptError {
    let mut msg = String::new();
    vm.write_exception(&mut msg, &err).unwrap();
    ScriptError::RuntimeError(msg)
}

#[derive(Debug, Default, Copy, Clone)]
pub struct PythonScriptEngine {}

impl ScriptEngine for PythonScriptEngine {
    type Script = PythonScript;

    fn eval(
        &self,
        script: &Self::Script,
        args: Vec<ScriptValue>,
    ) -> Result<ScriptValue, ScriptError> {
        send_python_msg_sync(PythonMsgData::Script(*script, args))?.try_into()
    }

    fn eval_in_query(
        &self,
        script: &Self::Script,
        args: Vec<ScriptQueryValue>,
        info: RefCell<ScriptTreeInfo>,
    ) -> Result<ScriptQueryValue, ScriptError> {
        let mut script_args: Vec<PythonScriptQueryArg> = vec![];
        for a in args {
            let b = match a {
                ScriptQueryValue::Simple(v) => PythonScriptQueryArg::Value(v),
                ScriptQueryValue::Node(n) => {
                    PythonScriptQueryArg::Node(ScriptNode::new(info.clone(), n))
                }
            };
            script_args.push(b);
        }

        let resp = send_python_msg_sync(PythonMsgData::ScriptInQuery(*script, script_args))?;
        let value: ScriptValue = resp.try_into()?;
        Ok(ScriptQueryValue::Simple(value))
    }

    fn compile_function(
        &self,
        script: &str,
        file_name: String,
        fun_name: String,
    ) -> Result<Self::Script, ScriptError> {
        compile_function(script, file_name, fun_name)
    }

    fn compile_aspects(
        &self,
        script: &str,
        file_name: String,
    ) -> Result<HashMap<String, HashMap<String, Self::Script>>, ScriptError> {
        compile_aspects(script, file_name)
    }
}

fn interpreter_with_stdlib() -> Interpreter {
    Interpreter::with_init(Default::default(), |vm| {
        vm.add_native_module("yaml".to_string(), Box::new(stdlib::yaml::make_module));
        vm.add_native_module("os".to_string(), Box::new(stdlib::os::make_module));
        vm.add_native_module("path".to_string(), Box::new(stdlib::path::make_module));
        vm.add_native_module("re".to_string(), Box::new(stdlib::re::make_module));
        ScriptNode::make_class(&vm.ctx);
        ScriptSG::make_class(&vm.ctx);
    })
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
            ScriptValue::Scope(scope_id, scope_graph, ctx) => {
                ScriptSG::new(ctx, scope_graph, scope_id).to_pyobject(vm)
            }
        }
    }
}

impl TryInto<ScriptQueryValue> for PyObjectRef {
    type Error = ScriptError;

    fn try_into(self) -> Result<ScriptQueryValue, Self::Error> {
        if let Some(node) = self.payload::<ScriptNode>() {
            Ok(ScriptQueryValue::Node(node.node))
        } else {
            Ok(ScriptQueryValue::Simple(self.try_into()?))
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
        } else if let Some(script_sg) = self.payload::<ScriptSG>() {
            ScriptValue::Scope(
                script_sg.scope_id,
                script_sg.scope_graph.clone(),
                script_sg.ctx.clone(),
            )
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
    use indoc::indoc;
    use maplit::{btreemap, hashmap, hashset};

    use crate::{
        builtin_langs::{get_builtin_lang, parser::BuiltinParserRunner, BuiltinLang},
        core::{
            source::Source,
            spec::{Spec, Syntax},
        },
        land::sylva::Sylva,
        query::{RawTreeInfoBuilder, SylvaNode, TreeInfoBuilder},
    };

    use super::*;

    #[test]
    fn script_from_fun() {
        let python_module = r#"
import path

def value():
    return 'directory'

def hello(file_name: str):
    return path.join(value(), file_name)
"#;

        let script =
            compile_function(python_module, "test.py".to_string(), "hello".to_string()).unwrap();

        let engine = PythonScriptEngine {};

        let value = engine
            .eval(&script, vec![ScriptValue::Str("file".to_string())])
            .unwrap();

        assert_eq!(value, ScriptValue::Str("directory/file".to_string()));
    }

    #[test]
    fn collect_aspect() {
        let python_module = r#"
@Expr.aspect1()
def my_aspect_expr():
    return 'Expr'
    
@Expr.aspect2()
def my_aspect2_expr2():
    return 'Expr2'

@Statement.aspect1()
def my_aspect_statement():
    return 'Statement'
"#;

        let invokables = compile_aspects(python_module, "aspect_test.py".to_string()).unwrap();

        assert_eq!(
            hashset! {"aspect1".to_string(), "aspect2".to_string()},
            invokables.keys().cloned().collect()
        );

        assert_eq!(
            hashset! {"Expr".to_string(), "Statement".to_string()},
            invokables["aspect1"].keys().cloned().collect()
        );

        assert_eq!(
            hashset! {"Expr".to_string()},
            invokables["aspect2"].keys().cloned().collect()
        );
    }

    #[test]
    fn yaml_loads_string() {
        test_yaml_loads("hello", ScriptValue::Str("hello".to_string()));
    }

    #[test]
    fn yaml_loads_int() {
        test_yaml_loads("42", ScriptValue::Integer(42));
    }

    #[test]
    fn yaml_loads_bool() {
        test_yaml_loads("true", ScriptValue::Bool(true));
    }

    #[test]
    fn yaml_loads_seq() {
        test_yaml_loads(
            "['hello', false]",
            ScriptValue::List(vec![
                ScriptValue::Str("hello".to_string()),
                ScriptValue::Bool(false),
            ]),
        )
    }

    #[test]
    fn yaml_loads_mapping() {
        let doc = r#"
apiVersion: v1
metaData:
  name: test
"#;

        test_yaml_loads(
            doc,
            ScriptValue::Dict(btreemap! {
                "apiVersion".to_string() => ScriptValue::Str("v1".to_string()),
                "metaData".to_string() => ScriptValue::Dict(btreemap! {
                    "name".to_string() => ScriptValue::Str("test".to_string())
                })
            }),
        );
    }

    fn test_yaml_loads(document: &str, expected: ScriptValue) {
        let python_module = r"
import yaml

def value(doc):
    return yaml.loads(doc)
#";

        let engine = PythonScriptEngine::default();
        let script =
            compile_function(python_module, "test.py".to_string(), "value".to_string()).unwrap();

        let value = engine
            .eval(&script, vec![ScriptValue::Str(document.to_string())])
            .unwrap();

        assert_eq!(value, expected);
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

    #[test]
    fn test_node_fn_javascript() {
        let script_scr = indoc! {"
            def append_suffix(node):
                return node.function.text + ' from Python'
            "
        };

        let (lang_mappings, lang, _) = get_builtin_lang(BuiltinLang::Javascript);

        let syntax: Syntax = lang_mappings.types.as_slice().into();

        let runner = BuiltinParserRunner::new(lang, &syntax, lang_mappings);

        let source = Source::inline(
            "console.log(hello).to_string()".to_string(),
            "BUFFER".to_string(),
        );

        let tree = runner.run(source);
        let sylva = Sylva::new(hashmap! {"buffer".into() => tree });

        let spec = Spec::new(Default::default(), syntax);

        let node = SylvaNode {
            node: 5.into(),
            tree: 0.into(),
            sylva: 0.into(),
        };

        let mut tree_info = RawTreeInfoBuilder::new(&spec, &sylva).info_for_node(node);

        let engine = PythonScriptEngine::default();
        let script = compile_function(
            script_scr,
            "test.py".to_string(),
            "append_suffix".to_string(),
        )
        .unwrap();

        let script_result = engine
            .eval_in_query(
                &script,
                vec![ScriptQueryValue::Node(node)],
                RefCell::new(ScriptTreeInfo::new(&mut tree_info)),
            )
            .unwrap();

        assert_eq!(
            script_result,
            ScriptQueryValue::Simple(ScriptValue::Str("console.log from Python".to_string()))
        );
    }
}
