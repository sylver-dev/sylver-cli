use std::collections::BTreeMap;

use thiserror::Error;

pub mod python;

#[derive(Debug, Error)]
pub enum ScriptError {
    #[error("Unsupported type: {0}")]
    UnsupportedType(String),
    #[error("Failed to compile script {0}: {1}")]
    Compilation(String, String),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum ScriptValue {
    Integer(i64),
    Str(String),
    Dict(BTreeMap<String, ScriptValue>),
}

pub trait ScriptEngine {
    type Script;

    fn eval(
        &self,
        script: &Self::Script,
        args: Vec<ScriptValue>,
    ) -> Result<ScriptValue, ScriptError>;
}
