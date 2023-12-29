use std::collections::HashMap;

pub mod rules;

use crate::{
    core::source::Source,
    land::{sylva::SylvaId, Land},
    query::{
        eval_predicate,
        expr::{EvalCtx, EvalError, Expr},
        sylva_nodes, RawTreeInfoBuilder, SylvaNode,
    },
    report::Report,
};

use crate::script::python::PythonScriptEngine;
pub use rules::*;

pub fn parsing_errors(land: &Land) -> HashMap<&Source, &[Report]> {
    land.sylvae.iter().flat_map(|(_, s)| s.reports()).collect()
}

pub fn filter_sylva(
    land: &Land,
    script_engine: PythonScriptEngine,
    sylva_id: SylvaId,
    predicate: &Expr,
) -> Result<Vec<SylvaNode>, EvalError> {
    let sylva = land.sylva(sylva_id);
    let spec = land.sylva_spec(sylva_id);

    let mut ctx = EvalCtx::new(
        spec,
        RawTreeInfoBuilder::new(spec, sylva),
        land,
        script_engine,
    );

    let mut filtered_nodes = vec![];

    for node in sylva_nodes(land, sylva_id) {
        if eval_predicate(&mut ctx, node, predicate)? {
            filtered_nodes.push(node);
        }
    }

    Ok(filtered_nodes)
}
