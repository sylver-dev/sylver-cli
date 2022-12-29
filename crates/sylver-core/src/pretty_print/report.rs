use codespan_reporting::{
    diagnostic::{Diagnostic, Label, Severity},
    files::SimpleFiles,
    term::{
        self,
        termcolor::{BufferWriter, ColorChoice},
    },
};

use crate::{
    core::source::Source,
    report::{Report, ReportKind},
};

pub fn render_report(
    color: bool,
    report: &Report,
    source: &Source,
) -> Result<String, anyhow::Error> {
    let mut files = SimpleFiles::new();
    let file_id = files.add(source.path().display().to_string(), source.src());

    let diagnostic = build_diagnostic(report, file_id);

    let color_choice = if color {
        ColorChoice::Auto
    } else {
        ColorChoice::Never
    };
    let mut buffer = BufferWriter::stdout(color_choice).buffer();

    term::emit(&mut buffer, &Default::default(), &files, &diagnostic)?;

    Ok(String::from_utf8(buffer.into_inner())?)
}

pub fn build_diagnostic<FileId>(report: &Report, file_id: FileId) -> Diagnostic<FileId> {
    Diagnostic::new(report_severity(report))
        .with_code(&report.code)
        .with_message(&report.message)
        .with_labels(vec![Label::primary(
            file_id,
            report.position.start().txt_pos..report.position.end().txt_pos,
        )])
        .with_notes(report.note.iter().cloned().collect())
}

fn report_severity(report: &Report) -> Severity {
    match report.kind {
        ReportKind::Error => Severity::Error,
        ReportKind::Warning => Severity::Warning,
        ReportKind::Info => Severity::Note,
    }
}
