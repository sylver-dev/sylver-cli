use std::sync::Arc;

use anyhow::Context;

use sylver_core::{
    core::files_spec::FileSpec,
    land::{builder::LandBuilder, cmds::run_task, Land},
    pretty_print::tree::render_node,
    query::{language::compile::compile, SylvaNode},
    specs::loader::SylverLoader,
    state::SylverState,
};
use sylver_dsl::sylq::parse_query;

use crate::{
    cli::QueryCmd,
    repl::start_repl,
    shared::{build_sylva, print_land_reports},
};

pub fn query(state: Arc<SylverState>, loader: &SylverLoader, cmd: &QueryCmd) -> anyhow::Result<()> {
    let land = build_land(loader, cmd)?;
    let sylva = land.sylvae().next().expect("Missing sylva");
    let spec = land.sylva_spec(sylva);

    print_land_reports(state.settings.color_output, &land)?;

    if let Some(query_str) = &cmd.query {
        let query = parse_query(query_str).context("Failed to parse query")?;
        let query_task = compile(spec, &query).context("Failed to compile query")?;

        for value in run_task(&land, sylva, &query_task)? {
            let sylva_node: SylvaNode = value.try_into()?;
            let tree = land.sylva_node_tree(sylva_node);
            println!("{}", render_node(spec, tree, sylva_node.node));
        }

        Ok(())
    } else {
        start_repl(&land, sylva)
    }
}

fn build_land(loader: &SylverLoader, cmd: &QueryCmd) -> anyhow::Result<Land> {
    let mut builder = LandBuilder::new();

    let sources = loader.load_file_spec(&FileSpec {
        root: None,
        include: cmd.files.clone(),
        exclude: cmd.exclude.clone(),
    })?;

    build_sylva(loader, &mut builder, &cmd.language, sources)?;

    Ok(builder.build())
}
