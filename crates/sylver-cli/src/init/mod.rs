use std::sync::Arc;

use anyhow::Context;
use log::Logger;
use rustyline::hint::Hint;

use sylver_core::{
    script::python::PythonScriptEngine,
    specs::{stem::project::ProjectConfigStem, stem::project::ProjectStem},
    state::SylverState,
};

use crate::{cli::InitCmd, init::detect::ProjectDetector};

mod detect;

pub fn init(state: Arc<SylverState>, cmd: &InitCmd) -> anyhow::Result<()> {
    let detection_root = std::env::current_dir()?;

    let detector = ProjectDetector::new(
        state.settings.backend_url.clone(),
        Box::new(state.logger.clone()),
        PythonScriptEngine::default(),
    );

    let project_stems = detector.detect_builtin_lang_projects(&detection_root);

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
