use std::sync::Arc;

use itertools::*;

use sylver_core::{
    core::files_spec::FileSpec,
    land::{builder::LandBuilder, Land},
    specs::{
        loader::SylverLoader,
        stem::{location::StemLocation, ruleset::RuleSetStem},
    },
    state::SylverState,
};

use crate::{
    cli::{RulesetCmd, RulesetCmds, RulesetRun},
    shared::{build_sylva, verify_land},
};

pub fn ruleset_cmd(
    state: Arc<SylverState>,
    loader: &SylverLoader,
    cmd: &RulesetCmd,
) -> anyhow::Result<()> {
    match &cmd.command {
        RulesetCmds::Run(r) => run_ruleset(state, loader, r),
    }
}

fn run_ruleset(
    state: Arc<SylverState>,
    loader: &SylverLoader,
    cmd: &RulesetRun,
) -> anyhow::Result<()> {
    verify_land(
        state.settings.color_output,
        &build_land(loader, cmd)?,
        cmd.min_level.map(Into::into),
    )
}

fn build_land(loader: &SylverLoader, cmd: &RulesetRun) -> anyhow::Result<Land> {
    let sources = loader.load_file_spec(&FileSpec {
        include: cmd.files.clone(),
    })?;

    let mut builder = LandBuilder::new();

    let ruleset_stems: Vec<RuleSetStem> = cmd
        .rulesets
        .iter()
        .map(|path| loader.load_ruleset(&StemLocation::from(path.as_str())))
        .collect::<anyhow::Result<Vec<RuleSetStem>>>()?;

    let ruleset_per_lang = ruleset_stems
        .into_iter()
        .map(|stem| (stem.language.clone(), stem))
        .into_group_map();

    for (language, rulesets) in ruleset_per_lang {
        let sylva_id = build_sylva(loader, &mut builder, &language, sources.clone())?;

        for rs in rulesets {
            builder.add_ruleset(sylva_id, &rs)?;
        }
    }

    Ok(builder.build())
}
