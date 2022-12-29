use std::collections::{HashMap, HashSet};

use crate::{
    core::source::Source,
    land::{
        ruleset::{Rule, RuleSetId, RuleSeverity},
        sylva::SylvaId,
        Land,
    },
    query::{RawTreeInfoBuilder, SylvaNode},
    report::{Report, ReportKind},
    tree::info::{raw::RawTreeInfo, TreeInfo},
};

#[derive(Debug, Clone)]
pub struct RuleResult {
    pub ruleset: RuleSetId,
    pub rule_id: String,
    pub node: SylvaNode,
}

impl RuleResult {
    pub fn to_report(&self, land: &Land) -> Report {
        let spec = land.sylva_spec(self.node.sylva);

        let rule = self.rule(land);

        let kind = match rule.level {
            RuleSeverity::Warning => ReportKind::Warning,
            RuleSeverity::Error => ReportKind::Error,
            RuleSeverity::Info => ReportKind::Info,
        };

        let tree = land.sylva(self.node.sylva).tree(self.node.tree).unwrap();

        let info = RawTreeInfo::new(tree, &spec.syntax);

        Report {
            file_path: tree.source.path().to_owned(),
            code: self.rule_id.clone(),
            kind,
            position: info.node_pos(self.node.node),
            message: rule.message.clone(),
            note: rule.note.clone(),
        }
    }

    pub fn source<'l>(&self, land: &'l Land) -> &'l Source {
        let sylva = land.sylva(self.node.sylva);
        let tree = sylva.tree(self.node.tree);
        &tree.unwrap().source
    }

    pub fn rule<'l>(&self, land: &'l Land) -> &'l Rule {
        land.ruleset(self.ruleset)
            .get_rule(&self.rule_id)
            .unwrap_or_else(|| panic!("No rule named: {}", self.rule_id))
    }
}

pub fn exec_rules(land: &Land, min_level: Option<RuleSeverity>) -> anyhow::Result<Vec<RuleResult>> {
    let res: Vec<RuleResult> = land
        .sylvae()
        .filter_map(|sylva_id| {
            let rulesets = land.sylva_rules.get(&sylva_id)?;
            Some((sylva_id, rulesets))
        })
        .flat_map(|(sylva, rulesets)| rulesets.iter().map(move |ruleset| (sylva, ruleset)))
        .map(|(sylva, &ruleset)| verify_sylva(land, ruleset, min_level, sylva))
        .collect::<anyhow::Result<Vec<Vec<RuleResult>>>>()?
        .into_iter()
        .flatten()
        .collect();

    Ok(res)
}

fn verify_sylva(
    land: &Land,
    ruleset_id: RuleSetId,
    min_level: Option<RuleSeverity>,
    sylva_id: SylvaId,
) -> anyhow::Result<Vec<RuleResult>> {
    let sylva = land.sylva(sylva_id);
    let ruleset = land.ruleset(ruleset_id);
    let spec = land.sylva_spec(sylva_id);

    let builder = RawTreeInfoBuilder::new(spec, sylva);

    let results = ruleset.verify(builder.clone(), land, sylva_id, min_level)?;

    Ok(to_rule_results(ruleset_id, results))
}

fn to_rule_results(
    ruleset: RuleSetId,
    results: HashMap<String, HashSet<SylvaNode>>,
) -> Vec<RuleResult> {
    results
        .into_iter()
        .flat_map(|(rule_id, nodes)| nodes.into_iter().map(move |n| (rule_id.clone(), n)))
        .map(|(rule_id, node)| RuleResult {
            ruleset,
            rule_id,
            node,
        })
        .collect()
}
