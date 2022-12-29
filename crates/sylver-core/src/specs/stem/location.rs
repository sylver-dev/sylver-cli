use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};

static REPO_FILE_SEPARATOR: &str = "#";

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
pub enum GitRepoMetaData {
    Commit(String),
    Branch(String),
}

/// Location of a stem: either a local path or a git repository
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(from = "IntermediateStemLocation", into = "IntermediateStemLocation")]
pub enum StemLocation {
    Local(PathBuf),
    Git {
        /// Url of the git repository
        repo: String,
        /// Path of the stem within th repo
        file: PathBuf,
        /// Additional metadata: commit, branch...
        metadata: Option<GitRepoMetaData>,
    },
}

impl StemLocation {
    /// Build a new `StemLocation` for a local path.
    pub fn local(path: impl AsRef<OsStr>) -> StemLocation {
        StemLocation::Local(Path::new(&path).to_owned())
    }
}

// Justification for the indirection: if a `Local` variant contains a git url,
// it is transformed when calling `into`. (cf the `From` implementation bellow).
#[derive(Serialize, Deserialize)]
#[serde(untagged)]
enum IntermediateStemLocation {
    Local(String),
    Git {
        repo: String,
        file: PathBuf,
        metadata: Option<GitRepoMetaData>,
    },
}

impl From<IntermediateStemLocation> for StemLocation {
    fn from(intermediate: IntermediateStemLocation) -> Self {
        match intermediate {
            IntermediateStemLocation::Git {
                repo,
                file,
                metadata,
            } => StemLocation::Git {
                repo,
                file,
                metadata,
            },
            IntermediateStemLocation::Local(path) => path.as_str().into(),
        }
    }
}

impl From<StemLocation> for IntermediateStemLocation {
    fn from(stem: StemLocation) -> Self {
        match stem {
            StemLocation::Local(path) => {
                IntermediateStemLocation::Local(path.to_string_lossy().to_string())
            }
            StemLocation::Git {
                repo,
                file,
                metadata,
            } => IntermediateStemLocation::Git {
                repo,
                file,
                metadata,
            },
        }
    }
}

impl From<&str> for StemLocation {
    fn from(s: &str) -> Self {
        repo_location_from_str(s).unwrap_or_else(|| StemLocation::Local(s.into()))
    }
}

/// If the input string is of the form GIT_URL#file, return the corresponding
/// stem location. Otherwise return None.
pub fn repo_location_from_str(s: &str) -> Option<StemLocation> {
    let split: Vec<&str> = s.split(REPO_FILE_SEPARATOR).collect();

    match split.as_slice() {
        [url, file] if url::Url::parse(url).is_ok() => Some(StemLocation::Git {
            repo: url.to_string(),
            file: file.into(),
            metadata: None,
        }),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn git_repo_from_str_ok() {
        let repo_str = "https://github.com/geoffreycopin/my-language.git#language.syl";
        let parsed = repo_location_from_str(repo_str);

        assert_eq!(
            Some(StemLocation::Git {
                repo: "https://github.com/geoffreycopin/my-language.git".to_string(),
                file: "language.syl".into(),
                metadata: None,
            }),
            parsed
        );
    }

    #[test]
    fn git_repo_from_str_notok() {
        let repo_str = "../path/to/language.syl";
        let parsed = repo_location_from_str(repo_str);

        assert_eq!(None, parsed);
    }
}
