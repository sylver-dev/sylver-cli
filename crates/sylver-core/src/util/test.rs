use std::path::PathBuf;

use temp_dir::TempDir;

pub fn create_tmp_child(dir: &TempDir, name: &str, content: &str) -> std::io::Result<PathBuf> {
    let path = dir.child(name);
    std::fs::write(&path, content)?;
    Ok(path)
}
