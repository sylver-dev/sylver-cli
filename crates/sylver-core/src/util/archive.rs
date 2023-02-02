use std::io::{Cursor, Read, Seek, Write};

use anyhow::Context;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ArchiveFile {
    pub name: String,
    pub content: String,
}

pub fn write_archive_to_vec(
    files: impl IntoIterator<Item = ArchiveFile>,
) -> anyhow::Result<Vec<u8>> {
    let mut cursor = Cursor::new(Vec::new());
    write_archive(&mut cursor, files)?;
    Ok(cursor.into_inner())
}

pub fn write_archive<W: Write + Seek>(
    stream: &mut W,
    files: impl IntoIterator<Item = ArchiveFile>,
) -> anyhow::Result<()> {
    let mut zip = zip::ZipWriter::new(stream);

    for file in files {
        zip.start_file(&file.name, Default::default())
            .with_context(|| format!("failed to create archive file {}", &file.name))?;
        zip.write_all(file.content.as_bytes())
            .with_context(|| format!("failed to write archive file {}", &file.name))?;
    }

    zip.finish()?;

    Ok(())
}

pub fn read_archive(bytes: &[u8]) -> anyhow::Result<Vec<ArchiveFile>> {
    let cursor = Cursor::new(bytes);
    let mut archive = zip::ZipArchive::new(cursor).context("failed to open archive")?;
    let mut files = Vec::new();

    for i in 0..archive.len() {
        let f = archive.by_index(i).unwrap();

        let name = f.name().to_string();

        let file_content = f
            .bytes()
            .collect::<Result<Vec<u8>, _>>()
            .with_context(|| "failed to read archive file".to_string())?;

        if let Ok(content) = String::from_utf8(file_content) {
            files.push(ArchiveFile { name, content });
        }
    }

    Ok(files)
}
