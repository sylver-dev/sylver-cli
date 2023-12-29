use std::collections::{HashMap, HashSet};
use std::ops::DerefMut;
use std::sync::RwLock;

use id_vec::IdVec;

use crate::semantic::names::SylvaScopes;
use crate::{
    core::{
        source::SourceTree,
        spec::{Spec, SpecId},
    },
    query::SylvaNode,
};

use self::{
    ruleset::{RuleSet, RuleSetId},
    sylva::{Sylva, SylvaId},
};

pub mod builder;
pub mod cmds;
pub mod ruleset;
pub mod sylva;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum LandSpecId {
    BuiltinLangId(SpecId),
    CustomLangId(SpecId),
}

impl LandSpecId {
    pub fn spec_id(self) -> SpecId {
        match self {
            LandSpecId::BuiltinLangId(id) | LandSpecId::CustomLangId(id) => id,
        }
    }
}

#[derive(Debug)]
pub struct Land {
    sylvae: IdVec<Sylva>,
    rulesets: IdVec<RuleSet>,
    specs: IdVec<Spec>,
    sylva_spec: HashMap<SylvaId, LandSpecId>,
    sylva_rules: HashMap<SylvaId, HashSet<RuleSetId>>,
    sylva_scopes: HashMap<SylvaId, RwLock<SylvaScopes>>,
}

impl Land {
    pub fn sylva(&self, id: SylvaId) -> &Sylva {
        &self.sylvae[id.into()]
    }

    pub fn sylva_scopes_mut(&'_ self, id: SylvaId) -> impl DerefMut<Target = SylvaScopes> + '_ {
        self.sylva_scopes
            .get(&id)
            .unwrap()
            .write()
            .expect("poisoned sylva scopes lock")
    }

    pub fn spec(&self, id: LandSpecId) -> &Spec {
        &self.specs[id.spec_id().into()]
    }

    pub fn ruleset(&self, id: RuleSetId) -> &RuleSet {
        &self.rulesets[id.into()]
    }

    pub fn sylva_rulesets(&self, id: SylvaId) -> HashSet<&RuleSet> {
        self.sylva_rules
            .get(&id)
            .unwrap()
            .iter()
            .map(|&ruleset_id| self.ruleset(ruleset_id))
            .collect()
    }

    pub fn sylva_spec(&self, id: SylvaId) -> &Spec {
        self.spec(self.sylva_spec_id(id))
    }

    pub fn sylva_spec_id(&self, id: SylvaId) -> LandSpecId {
        *self.sylva_spec.get(&id).unwrap()
    }

    pub fn sylvae(&'_ self) -> impl '_ + Iterator<Item = SylvaId> {
        self.sylvae.ids().map(Into::into)
    }

    pub fn sylva_node_tree(&self, sylva_node: SylvaNode) -> &SourceTree {
        let sylva = self.sylva(sylva_node.sylva);
        sylva.source_tree(sylva_node.tree).unwrap()
    }
}
