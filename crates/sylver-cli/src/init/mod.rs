use anyhow::Context;
use rustyline::hint::Hint;
use std::sync::Arc;

use sylver_core::specs::stem::project::ProjectStem;
use sylver_core::{specs::stem::project::ProjectConfigStem, state::SylverState};
use sylver_script::python::PythonScriptEngine;

use crate::{cli::InitCmd, init::detect::detect_builtin_lang_projects};

mod detect;

pub fn init(state: Arc<SylverState>, cmd: &InitCmd) -> anyhow::Result<()> {
    let detection_root = std::env::current_dir()?;
    let script_engine = PythonScriptEngine::default();

    let project_stems =
        detect_builtin_lang_projects(&script_engine, state.logger.as_ref(), &detection_root)?;

    create_dir_and_config(state, cmd, project_stems)?;

    Ok(())
}

fn create_dir_and_config(
    state: Arc<SylverState>,
    cmd: &InitCmd,
    project_stems: Vec<ProjectStem>,
) -> anyhow::Result<()> {
    std::fs::create_dir(".sylver").context("failed to create .sylver dir")?;
    state.logger.success("Created .sylver directory");

    let top_project = ProjectConfigStem::Nested {
        projects: project_stems,
    };

    std::fs::write(
        &cmd.config_path,
        serde_yaml::to_string(&top_project).unwrap(),
    )
    .context("Failed to write config file")?;

    state.logger.success(&format!(
        "Created config file at {}",
        cmd.config_path.display()
    ));

    Ok(())
}
