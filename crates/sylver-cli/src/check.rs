use std::{collections::HashMap, path::Path, sync::Arc};

use anyhow::bail;

use sylver_core::{
    core::files_spec::FileSpec,
    land::{builder::LandBuilder, ruleset::RuleSetId, Land, LandSpecId},
    specs::{
        loader::SylverLoader,
        stem::{location::StemLocation, project::ProjectLang},
    },
    state::SylverState,
};

use crate::{
    cli::CheckCmd,
    shared::{build_sylva, print_land_reports, run_land_rules},
    upload::ReportUploader,
};

pub struct CheckLandData {
    pub land: Land,
    pub langs: HashMap<LandSpecId, ProjectLang>,
    pub rulesets: HashMap<RuleSetId, StemLocation>,
}

pub fn check(state: Arc<SylverState>, loader: &SylverLoader, cmd: &CheckCmd) -> anyhow::Result<()> {
    match &state.locations.config_file {
        Some(f) => run_check(state.clone(), loader, f, cmd),
        None => bail!("Missing configuration file"),
    }
}

fn run_check(
    state: Arc<SylverState>,
    loader: &SylverLoader,
    config_path: &Path,
    cmd: &CheckCmd,
) -> anyhow::Result<()> {
    let check_data = build_check_state(loader, config_path)?;

    let min_level = if cmd.upload { None } else { cmd.min_level };

    print_land_reports(state.settings.color_output, &check_data.land)?;
    let res = run_land_rules(
        state.settings.color_output,
        &check_data.land,
        min_level.map(Into::into),
    )?;

    if cmd.upload {
        ReportUploader::new(loader, cmd, &check_data).upload(&res);
    }

    if !res.is_empty() {
        std::process::exit(1);
    }

    Ok(())
}

fn build_check_state(loader: &SylverLoader, config_path: &Path) -> anyhow::Result<CheckLandData> {
    let config = loader.load_config(config_path)?;
    let mut builder = LandBuilder::new();
    let mut sylva_langs = HashMap::new();
    let mut rulesets = HashMap::new();

    for project in config.projects() {
        let sources = loader.load_file_spec(&FileSpec {
            include: project.include.clone(),
            exclude: project.exclude.clone(),
        })?;

        let sylva = build_sylva(loader, &mut builder, &project.language, sources)?;

        sylva_langs.insert(sylva, project.language.clone());

        for ruleset in &project.rulesets {
            let rule_set_id = builder.add_ruleset(sylva, &loader.load_ruleset(ruleset)?)?;
            rulesets.insert(rule_set_id, ruleset.clone());
        }
    }

    let land = builder.build();

    let langs = sylva_langs
        .into_iter()
        .map(|(sylva, lang)| (land.sylva_spec_id(sylva), lang))
        .collect();

    Ok(CheckLandData {
        land,
        langs,
        rulesets,
    })
}
