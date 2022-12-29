use std::path::PathBuf;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize, Default)]
pub struct LanguageStem {
    pub id: String,
    pub spec: PathBuf,
}
