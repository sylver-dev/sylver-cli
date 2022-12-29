use std::collections::HashMap;

use id_vec::IdVec;

use crate::{
    core::spec::{Spec, SpecId},
    land::{
        ruleset::RuleSetId,
        sylva::{Sylva, SylvaId},
        LandSpecId,
    },
    specs::stem::ruleset::RuleSetStem,
};

use super::{ruleset::RuleSet, Land};

#[derive(Debug)]
pub struct LandBuilder {
    land: Land,
}

impl LandBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_spec(&mut self, spec: Spec) -> SpecId {
        self.land.specs.insert(spec).into()
    }

    pub fn add_sylva(&mut self, sylva: Sylva, spec_id: LandSpecId) -> anyhow::Result<SylvaId> {
        let sylva_id = self.land.sylvae.insert(sylva).into();
        self.land.sylva_spec.insert(sylva_id, spec_id);
        Ok(sylva_id)
    }

    pub fn add_ruleset(&mut self, sylva: SylvaId, stem: &RuleSetStem) -> anyhow::Result<RuleSetId> {
        let spec_id = *self.land.sylva_spec.get(&sylva).unwrap();
        let spec = self.land.spec(spec_id);

        let ruleset = RuleSet::from_stem(spec, stem)?;
        let ruleset_id = self.land.rulesets.insert(ruleset).into();

        self.land
            .sylva_rules
            .entry(sylva)
            .or_default()
            .insert(ruleset_id);

        Ok(ruleset_id)
    }

    pub fn build(self) -> Land {
        self.land
    }
}

impl Default for LandBuilder {
    fn default() -> Self {
        LandBuilder {
            land: Land {
                sylvae: IdVec::new(),
                rulesets: IdVec::new(),
                specs: IdVec::new(),
                sylva_spec: HashMap::new(),
                sylva_rules: HashMap::new(),
            },
        }
    }
}
