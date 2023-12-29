use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashMap, HashSet},
};

use anyhow::anyhow;
use id_vec::Id;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use sylver_dsl::sylq::parse_query;

use crate::{
    core::spec::Spec,
    id_type,
    land::{sylva::SylvaId, Land},
    query::{
        eval_predicate,
        expr::{EvalCtx, EvalError, Expr},
        language::compile::compile,
        sylva_nodes, RawTreeInfoBuilder, SylvaNode,
    },
    script::python::PythonScriptEngine,
    specs::stem::ruleset::{RuleSetStem, RuleStem},
};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RuleCategory {
    Style,
    Smell,
    Deprecated,
    Bug,
    Error,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Rule {
    predicate: Expr,
    pub message: String,
    pub category: RuleCategory,
    pub note: Option<String>,
}

impl Rule {
    fn from_stem(spec: &Spec, stem: &RuleStem) -> anyhow::Result<Rule> {
        let query_ast = parse_query(&stem.query)?;

        Ok(Rule {
            message: stem.message.clone(),
            predicate: compile(spec, &query_ast)?,
            category: stem.category,
            note: stem.note.clone(),
        })
    }
}

id_type!(RuleSetId: RuleSet);

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct RuleSet {
    rules: BTreeMap<String, Rule>,
}

impl RuleSet {
    pub fn new(rules: BTreeMap<String, Rule>) -> RuleSet {
        RuleSet { rules }
    }

    pub fn verify<'b>(
        &self,
        builder: RawTreeInfoBuilder<'b>,
        land: &'b Land,
        sylva_id: SylvaId,
    ) -> anyhow::Result<HashMap<String, HashSet<SylvaNode>>> {
        let mut rule_matches: HashMap<String, HashSet<SylvaNode>> = HashMap::new();

        let evaluation_results: Vec<Result<Vec<(String, SylvaNode)>, EvalError>> = self
            .rules
            .par_iter()
            .map(|(name, rule)| {
                let spec = land.sylva_spec(sylva_id);
                let mut ctx =
                    EvalCtx::new(spec, builder.clone(), land, PythonScriptEngine::default());
                let mut results = Vec::new();

                for sylva_node in sylva_nodes(land, sylva_id) {
                    let is_match = eval_predicate(&mut ctx, sylva_node, &rule.predicate)?;

                    if is_match {
                        results.push((name.clone(), sylva_node));
                    }
                }

                Ok(results)
            })
            .collect();

        evaluation_results
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .for_each(|(rule_name, sylva_node)| {
                rule_matches
                    .entry(rule_name)
                    .or_default()
                    .insert(sylva_node);
            });

        Ok(rule_matches)
    }

    pub fn get_rule(&self, rule_id: &str) -> Option<&Rule> {
        self.rules.get(rule_id)
    }

    pub fn from_stem(spec: &Spec, stem: &RuleSetStem) -> anyhow::Result<RuleSet> {
        let mut rules = BTreeMap::new();

        for rule_stem in &stem.rules {
            let rule = Rule::from_stem(spec, rule_stem)?;
            if rules.insert(rule_stem.id.clone(), rule).is_some() {
                return Err(anyhow!("Rule {} is defined multiple times", rule_stem.id));
            }
        }

        Ok(RuleSet { rules })
    }
}
