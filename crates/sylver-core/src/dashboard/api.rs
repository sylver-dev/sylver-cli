use serde::{Deserialize, Serialize};

use crate::{
    builtin_langs::BuiltinLang,
    core::pos::{InclPosRange, Pos},
    specs::stem::location::StemLocation,
};

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct NewReportDTO {
    pub language: ReportLanguage,
    pub commit: String,
    pub branch: String,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum ReportLanguage {
    Builtin(BuiltinLang),
    Custom(ReportCustomLanguage),
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct ReportCustomLanguage {
    pub name: String,
    pub stem: StemLocation,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct ReportDTO {
    pub id: i64,
    pub repo: i64,
    pub commit: String,
    pub branch: String,
    pub language: ReportLanguage,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct DiagnosticDTO {
    pub id: i64,
    pub report_id: i64,
    pub rule_set: StemLocation,
    pub rule: String,
    pub description: String,
    pub file: String,
    pub position: Position,
    pub repo_name: String,
    pub repo_owner: String,
    pub file_url: String,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct NewDiagnosticDTO {
    pub report_id: i64,
    pub rule_set: StemLocation,
    pub rule: String,
    pub description: String,
    pub file: String,
    pub position: Position,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct Position {
    pub start_line: usize,
    pub start_col: usize,
    pub start_txt_pos: usize,
    pub end_line: usize,
    pub end_col: usize,
    pub end_txt_pos: usize,
}

impl From<Position> for InclPosRange {
    fn from(p: Position) -> Self {
        InclPosRange::new(
            Pos::new((p.start_line, p.start_col), p.start_txt_pos),
            Pos::new((p.end_line, p.end_col), p.end_txt_pos),
        )
        .unwrap()
    }
}

impl From<InclPosRange> for Position {
    fn from(p: InclPosRange) -> Self {
        Position {
            start_line: p.start().line,
            start_col: p.start().col,
            start_txt_pos: p.start().txt_pos,
            end_line: p.end().line,
            end_col: p.end().col,
            end_txt_pos: p.end().txt_pos,
        }
    }
}
