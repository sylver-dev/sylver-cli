use std::path::PathBuf;

use crate::core::pos::InclPosRange;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum ReportKind {
    Error,
    Warning,
    Info,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Report {
    pub file_path: PathBuf,
    pub code: String,
    pub kind: ReportKind,
    pub position: InclPosRange,
    pub message: String,
    pub note: Option<String>,
}
