use std::sync::Arc;
use sylver_core::state::SylverState;
use sylver_script::python::PythonScriptEngine;

use crate::init::detect::detect_builtin_lang_projects;

mod detect;

pub fn init(state: Arc<SylverState>) -> anyhow::Result<()> {
    let mut detection_root = std::env::current_dir()?;
    let script_engine = PythonScriptEngine::default();

    detect_builtin_lang_projects(&script_engine, state.logger.as_ref(), &detection_root)?;

    Ok(())
}
