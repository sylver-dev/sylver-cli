use std::collections::BTreeMap;

use derive_more::From;
use thiserror::Error;

use sylver_core::query::{expr::EvalCtx, RawTreeInfoBuilder, SylvaNode};

pub mod python;

#[derive(Debug, Error)]
pub enum ScriptError {
    #[error("Runtime error: {0}")]
    RuntimeError(String),
    #[error("Unsupported type: {0}")]
    UnsupportedType(String),
    #[error("Expected a {0}, but got: {1:?}")]
    InvalidType(String, ScriptValue),
    #[error("Failed to compile script {0}: {1}")]
    Compilation(String, String),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, From)]
pub enum ScriptValue {
    Bool(bool),
    Integer(i64),
    Str(String),
    Dict(BTreeMap<String, ScriptValue>),
    List(Vec<ScriptValue>),
}

impl TryInto<bool> for ScriptValue {
    type Error = ScriptError;

    fn try_into(self) -> Result<bool, Self::Error> {
        match self {
            ScriptValue::Bool(bool_value) => Ok(bool_value),
            _ => Err(ScriptError::InvalidType("bool".to_string(), self)),
        }
    }
}

impl TryInto<i64> for ScriptValue {
    type Error = ScriptError;

    fn try_into(self) -> Result<i64, Self::Error> {
        match self {
            ScriptValue::Integer(int_value) => Ok(int_value),
            _ => Err(ScriptError::InvalidType("integer".to_string(), self)),
        }
    }
}

impl TryInto<String> for ScriptValue {
    type Error = ScriptError;

    fn try_into(self) -> Result<String, Self::Error> {
        match self {
            ScriptValue::Str(str_value) => Ok(str_value),
            _ => Err(ScriptError::InvalidType("string".to_string(), self)),
        }
    }
}

impl TryInto<BTreeMap<String, ScriptValue>> for ScriptValue {
    type Error = ScriptError;

    fn try_into(self) -> Result<BTreeMap<String, ScriptValue>, Self::Error> {
        match self {
            ScriptValue::Dict(map) => Ok(map),
            _ => Err(ScriptError::InvalidType("dict".to_string(), self)),
        }
    }
}

impl TryInto<Vec<ScriptValue>> for ScriptValue {
    type Error = ScriptError;

    fn try_into(self) -> Result<Vec<ScriptValue>, Self::Error> {
        match self {
            ScriptValue::List(list) => Ok(list),
            _ => Err(ScriptError::InvalidType("list".to_string(), self)),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, From)]
pub enum ScriptQueryValue {
    Simple(ScriptValue),
    Node(SylvaNode),
}

pub trait ScriptEngine {
    type Script;

    fn eval(
        &self,
        script: &Self::Script,
        args: Vec<ScriptValue>,
    ) -> Result<ScriptValue, ScriptError>;

    fn eval_in_query<'c>(
        &self,
        script: &Self::Script,
        args: Vec<ScriptQueryValue>,
        ctx: &mut EvalCtx<'c, RawTreeInfoBuilder<'c>>,
    ) -> Result<ScriptQueryValue, ScriptError>;

    fn compile_function(
        &self,
        script: &str,
        file_name: &str,
        fun_name: &str,
    ) -> Result<Self::Script, ScriptError>;
}
