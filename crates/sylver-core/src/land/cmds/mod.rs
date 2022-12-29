use std::collections::HashMap;

pub mod rules;

use crate::{
    core::source::Source,
    land::{sylva::SylvaId, Land},
    query::{
        expr::{EvalError, Value},
        RawTreeInfoBuilder, Task,
    },
    report::Report,
};

pub use rules::*;

pub fn parsing_errors(land: &Land) -> HashMap<&Source, &[Report]> {
    land.sylvae.iter().flat_map(|(_, s)| s.reports()).collect()
}

pub fn run_task<'l>(
    land: &'l Land,
    sylva_id: SylvaId,
    task: &Task,
) -> Result<Vec<Value<'static>>, EvalError> {
    let sylva = land.sylva(sylva_id);
    let spec = land.sylva_spec(sylva_id);

    Ok(task
        .run(RawTreeInfoBuilder::new(spec, sylva), land, sylva_id)?
        .into_iter()
        .map(|v| v.to_static())
        .collect())
}
