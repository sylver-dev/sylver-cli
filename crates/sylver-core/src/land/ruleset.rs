use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashMap, HashSet},
};

use anyhow::{anyhow, Context};
use id_vec::Id;
use serde::{Deserialize, Serialize};
use sylver_dsl::sylq::parse_query;

use crate::{
    core::spec::Spec,
    id_type,
    land::{sylva::SylvaId, Land},
    query::{language::compile::compile, SylvaNode, Task, TreeInfoBuilder},
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
    predicate: Task,
    pub message: String,
    pub category: RuleCategory,
    pub note: Option<String>,
}

impl Rule {
    fn verify<'b, B: 'b + TreeInfoBuilder<'b>>(
        &self,
        builder: B,
        land: &'b Land,
        sylva_id: SylvaId,
    ) -> anyhow::Result<HashSet<SylvaNode>> {
        Ok(self
            .predicate
            .run(builder, land, sylva_id)
            .with_context(|| "Evaluation error")?
            .into_iter()
            .map(TryInto::try_into)
            .collect::<Result<HashSet<SylvaNode>, _>>()?)
    }

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

    pub fn verify<'b, B: 'b + Clone + TreeInfoBuilder<'b>>(
        &self,
        builder: B,
        land: &'b Land,
        sylva_id: SylvaId,
    ) -> anyhow::Result<HashMap<String, HashSet<SylvaNode>>> {
        let mut result: HashMap<String, HashSet<SylvaNode>> = HashMap::new();

        for (rule_id, rule) in &self.rules {
            let flagged = rule.verify(builder.clone(), land, sylva_id)?;

            if !flagged.is_empty() {
                result.entry(rule_id.clone()).or_default().extend(flagged);
            }
        }

        Ok(result)
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
