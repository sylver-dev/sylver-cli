use std::sync::Arc;

use anyhow::Result;

use sylver_core::{
    core::{
        source::{source_from_file, Source, SourceTree},
        spec::{spec_from_files, Syntax},
    },
    parsing::parser_runner::ParserRunner,
    pretty_print::{render_report, tree::TreePPrint},
    report::Report,
    state::SylverState,
    tree::info::raw::RawTreeInfo,
};

use crate::ParseCmd;

pub fn parse(state: Arc<SylverState>, cmd: &ParseCmd) -> Result<()> {
    let spec = spec_from_files(&state.script_engine, None, &cmd.spec)?;
    let parser_runner = ParserRunner::new(
        &cmd.rule.clone().unwrap_or_else(|| "main".to_string()),
        &spec.syntax,
    )?;

    let source = source_from_file(&cmd.file)?;

    let res = parser_runner.run_once(source);

    print_reports(state, &res.reports, &res.tree.source);
    print_tree(&res.tree, &spec.syntax);

    Ok(())
}

fn print_tree(tree: &SourceTree, syntax: &Syntax) {
    println!(
        "{}",
        TreePPrint::new(RawTreeInfo::new(tree, syntax)).render()
    );
}

pub fn print_reports(state: Arc<SylverState>, reports: &[Report], source: &Source) {
    for r in reports {
        println!(
            "{}",
            render_report(state.settings.color_output, r, source).unwrap()
        );
    }
}
