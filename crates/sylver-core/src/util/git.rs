use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::anyhow;

use log::Logger;

#[derive(Debug, Clone, Default)]
pub struct GitClient {}

impl GitClient {
    pub fn current_branch() -> anyhow::Result<String> {
        run_git(["branch", "--show-current"]).map(|s| s.trim_end().to_string())
    }

    pub fn current_commit() -> anyhow::Result<String> {
        run_git(["rev-parse", "HEAD"]).map(|s| s.trim_end().to_string())
    }

    pub fn clone_repo(
        &self,
        logger: &dyn Logger,
        artefact_type: &str,
        url: &str,
        repos_dir: &Path,
    ) -> anyhow::Result<PathBuf> {
        let clone_in = repo_clone_dir(url, repos_dir);

        if repo_dir_empty(&clone_in)? {
            let _spinner = logger.scoped(
                &format!("Cloning {artefact_type} from {url}"),
                Some(&format!("Cloned {artefact_type} from {url}",)),
            );

            run_git([OsStr::new("clone"), OsStr::new(url), clone_in.as_os_str()])?;
        }

        Ok(clone_in)
    }
}

fn repo_clone_dir(url: &str, repo_dir: &Path) -> PathBuf {
    let separator_regex = fancy_regex::Regex::new(r#"/|\\"#).unwrap();
    let dir_name = separator_regex.replace_all(url, "_").into_owned();
    repo_dir.join(Path::new(&dir_name))
}

fn repo_dir_empty(repo_dir: &Path) -> anyhow::Result<bool> {
    Ok(!repo_dir.exists() || repo_dir.read_dir()?.next().is_none())
}

fn run_git<I, S>(args: I) -> anyhow::Result<String>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let output = Command::new("git").args(args).output()?;

    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    } else {
        let msg = String::from_utf8_lossy(&output.stderr).into_owned();
        Err(anyhow!(msg))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn http_repo_url_clone_dir() {
        let repo_url = "https://github.com/torvalds/linux.git";
        let repos_dir = Path::new(".sylver/dl/repos");
        let cloned_in = repo_clone_dir(repo_url, repos_dir);

        assert_eq!(
            cloned_in,
            Path::new(".sylver/dl/repos/https:__github.com_torvalds_linux.git")
        );
    }
}
