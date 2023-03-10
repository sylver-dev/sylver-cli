use serde::{Deserialize, Serialize};

use crate::{land::ruleset::RuleCategory, specs::stem::project::ProjectLang};

/// Static description of a ruleset
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
pub struct RuleSetStem {
    pub id: String,
    pub language: ProjectLang,
    pub rules: Vec<RuleStem>,
}

/// Static description of a rule.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
pub struct RuleStem {
    /// Short 'technical' id.
    pub id: String,
    /// User friendly diagnostic message.
    pub message: String,
    /// Code of the query matching violating nodes.
    pub query: String,
    /// Category of the lint.
    pub category: RuleCategory,
    /// Additional node
    pub note: Option<String>,
}
