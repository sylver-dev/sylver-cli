use fancy_regex::Regex;
use semver::Version;
use std::fmt::{Display, Formatter};
use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};

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
    Registry {
        author: String,
        name: String,
        version: Option<Version>,
    },
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

fn format_registry_location(author: &str, name: &str, version: Option<&Version>) -> String {
    let mut res = format!("@{author}/{name}");

    if let Some(version) = version {
        res.push_str(&format!(":{version}"));
    }

    res
}

// Justification for the indirection: if a `Local` variant contains a git url,
// it is transformed when calling `into`. (cf the `From` implementation bellow).
#[derive(Serialize, Deserialize)]
#[serde(untagged)]
enum IntermediateStemLocation {
    Inline(String),
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
            IntermediateStemLocation::Inline(path) => path.as_str().into(),
        }
    }
}

impl From<StemLocation> for IntermediateStemLocation {
    fn from(stem: StemLocation) -> Self {
        match stem {
            StemLocation::Local(path) => {
                IntermediateStemLocation::Inline(path.to_string_lossy().to_string())
            }
            StemLocation::Registry {
                author,
                name,
                version,
            } => IntermediateStemLocation::Inline(format_registry_location(
                &author,
                &name,
                version.as_ref(),
            )),
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

impl Display for StemLocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            StemLocation::Local(path) => write!(f, "{}", path.to_string_lossy()),
            StemLocation::Registry {
                author,
                name,
                version,
            } => write!(
                f,
                "{}",
                format_registry_location(author, name, version.as_ref())
            ),
            StemLocation::Git { repo, file, .. } => {
                write!(f, "{}#{}", repo, file.to_string_lossy())
            }
        }
    }
}

impl From<&str> for StemLocation {
    fn from(s: &str) -> Self {
        stem_location_from_str(s).unwrap_or_else(|| StemLocation::Local(s.into()))
    }
}

/// If the input string is of the form matches a registry or repository id, return the
/// corresponding `StemLocation`.
pub fn stem_location_from_str(s: &str) -> Option<StemLocation> {
    git_locaton_from_str(s).or_else(|| registry_location_from_str(s))
}

pub fn git_locaton_from_str(s: &str) -> Option<StemLocation> {
    let git_regex = Regex::new(r"^(?<repo>.*)#(?<file>.*)$").unwrap();

    if let Ok(Some(captures)) = git_regex.captures(s) {
        Some(StemLocation::Git {
            repo: captures.name("repo").unwrap().as_str().to_string(),
            file: PathBuf::from(captures.name("file").unwrap().as_str()),
            metadata: None,
        })
    } else {
        None
    }
}

pub fn registry_location_from_str(s: &str) -> Option<StemLocation> {
    let registry_regex = Regex::new(r"^@(?<author>.+)/(?<name>[^:]+)(?<version>:.+)?$").unwrap();

    if let Ok(Some(captures)) = registry_regex.captures(s) {
        Some(StemLocation::Registry {
            author: captures.name("author").unwrap().as_str().to_string(),
            name: captures.name("name").unwrap().as_str().to_string(),
            version: captures
                .name("version")
                .and_then(|v| v.as_str()[1..].parse().ok()),
        })
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn versioned_registry_location_from_str() {
        let registry_id = "@sylver/awesome-stem:1.0.0";
        let location = StemLocation::from(registry_id);

        assert_eq!(
            StemLocation::Registry {
                author: "sylver".to_string(),
                name: "awesome-stem".to_string(),
                version: Some(Version::new(1, 0, 0)),
            },
            location
        )
    }

    #[test]
    fn unversioned_registry_location_from_str() {
        let registry_id = "@sylver/awesome-stem";
        let location = StemLocation::from(registry_id);

        assert_eq!(
            StemLocation::Registry {
                author: "sylver".to_string(),
                name: "awesome-stem".to_string(),
                version: None,
            },
            location
        )
    }

    #[test]
    fn git_repo_from_str_ok() {
        let repo_str = "https://github.com/geoffreycopin/my-language.git#language.syl";
        let parsed = stem_location_from_str(repo_str);

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
        let parsed = stem_location_from_str(repo_str);

        assert_eq!(None, parsed);
    }
}
