use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
};

pub fn find_upward_path(mut current_dir: PathBuf, name: &OsStr) -> anyhow::Result<Option<PathBuf>> {
    let mut match_dir = dir_entry_with_name(&current_dir, name)?;

    while match_dir.is_none() && current_dir.parent().is_some() {
        current_dir = current_dir.parent().unwrap().to_owned();
        match_dir = dir_entry_with_name(&current_dir, name)?;
    }

    Ok(match_dir)
}

fn dir_entry_with_name(dir: &Path, name: &OsStr) -> anyhow::Result<Option<PathBuf>> {
    let candidate = dir.join(name);
    match std::fs::metadata(&candidate) {
        Ok(meta) if meta.is_dir() => Ok(Some(candidate)),
        _ => Ok(None),
    }
}

pub fn path_to_string(path: &Path) -> String {
    path.to_string_lossy().to_string()
}
