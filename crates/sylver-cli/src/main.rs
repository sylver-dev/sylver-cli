use std::sync::Arc;

use anyhow::Result;
use clap::Parser;

use log::{FancyLogger, Logger};

use sylver_core::{
    specs::loader::SylverLoader,
    state::{SylverSettings, SylverState},
};

use crate::{
    cli::{Cli, Commands, ParseCmd},
    parse::parse,
    query::query,
};

mod check;
mod cli;
mod init;
mod parse;
mod query;
mod repl;
mod ruleset;
mod shared;
mod upload;

fn main() -> Result<()> {
    let logger: Box<FancyLogger> = Box::default();

    let cmd = cli::Cli::parse();

    let conf = build_conf(&cmd);

    let res = {
        let state = Arc::new(SylverState::with_settings(logger.clone(), conf)?);
        eval(state, cmd)
    };

    if let Err(e) = res {
        logger.error(&format!("{}", e));
        std::process::exit(1);
    }

    Ok(())
}

fn eval(state: Arc<SylverState>, cmd: Cli) -> Result<()> {
    let loader = SylverLoader::from_state(state.clone());

    match cmd.command {
        Commands::Check(cmd) => check::check(state, &loader, &cmd)?,
        Commands::Parse(cmd) => parse(state, &cmd)?,
        Commands::Query(cmd) => query(state, &loader, &cmd)?,
        Commands::Ruleset(cmd) => ruleset::ruleset_cmd(state, &loader, &cmd)?,
    };

    Ok(())
}

fn build_conf(cmd: &Cli) -> SylverSettings {
    let config_override = match &cmd.command {
        Commands::Check(cmd) => cmd.config.clone(),
        _ => None,
    };

    SylverSettings {
        color_output: !cmd.no_color,
        config_override,
    }
}
