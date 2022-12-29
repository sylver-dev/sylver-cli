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
    for entry in dir.read_dir()? {
        let dir = entry?;
        let path = dir.path();

        if path.is_dir() && path.file_name() == Some(name) {
            return Ok(Some(path));
        }
    }

    Ok(None)
}

pub fn path_to_string(path: &Path) -> String {
    path.to_string_lossy().to_string()
}
