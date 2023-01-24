use anyhow::{bail, Context};
use std::{
    ffi::OsStr,
    fmt::Debug,
    path::{Path, PathBuf},
};

use log::{FancyLogger, Logger};

use crate::util::fs::find_upward_path;

pub static DEFAULT_SYLVER_CONFIG_NAMES: [&str; 2] = ["sylver.yml", "sylver.yaml"];

static SYLVER_DIR_NAME: &str = ".sylver";
static DL_DIR_NAME: &str = "dl";
static REPOS_DIR_NAME: &str = "repos";

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SylverSettings {
    pub color_output: bool,
    pub config_override: Option<PathBuf>,
    pub backend_url: String,
}

impl Default for SylverSettings {
    fn default() -> Self {
        SylverSettings {
            color_output: true,
            config_override: None,
            backend_url: "https://api.sylver.dev".to_string(),
        }
    }
}

/// Global configuration.
#[derive(Debug)]
pub struct SylverState<L: Logger = FancyLogger> {
    pub settings: SylverSettings,
    pub locations: Locations,
    pub logger: L,
}

impl<L: Logger> SylverState<L> {
    pub fn with_settings(logger: L, conf: SylverSettings) -> anyhow::Result<SylverState<L>> {
        Self::load_from(logger, conf, std::env::current_dir()?)
    }

    pub fn load(logger: L) -> anyhow::Result<SylverState<L>> {
        Self::load_from(logger, Default::default(), std::env::current_dir()?)
    }

    fn load_from(logger: L, settings: SylverSettings, dir: PathBuf) -> anyhow::Result<Self> {
        let locations = Locations::from_sylver_dir(&settings, sylver_dir_location(&dir))?;

        Ok(SylverState {
            settings,
            logger,
            locations,
        })
    }
}

fn sylver_dir_location(current_dir: &Path) -> PathBuf {
    match find_upward_path(current_dir.to_owned(), OsStr::new(SYLVER_DIR_NAME)) {
        Ok(Some(d)) => d,
        _ => current_dir.join(SYLVER_DIR_NAME),
    }
}

/// Paths of the subdirectories within the .sylver directory.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Locations {
    /// .sylver directory
    pub sylver_dir: PathBuf,
    /// Directory for cloning git repos.
    pub repos: PathBuf,
    /// sylver.yaml file... or it's equivalent
    pub config_file: Option<PathBuf>,
}

impl Locations {
    fn from_sylver_dir(
        settings: &SylverSettings,
        sylver_dir: PathBuf,
    ) -> anyhow::Result<Locations> {
        let repos = sylver_dir.join(DL_DIR_NAME).join(REPOS_DIR_NAME);

        let config_file = match &settings.config_override {
            Some(p) => {
                check_conf_file_exists(p)?;
                Some(p.clone())
            }
            None => get_config_location(&sylver_dir)?,
        };

        Ok(Locations {
            sylver_dir,
            repos,
            config_file,
        })
    }
}

fn get_config_location(sylver_dir: &Path) -> anyhow::Result<Option<PathBuf>> {
    for conf_name in DEFAULT_SYLVER_CONFIG_NAMES {
        let conf_file = sylver_dir.with_file_name(conf_name);
        if let Ok(Some(f)) = check_conf_file_exists(&conf_file) {
            return Ok(Some(f));
        }
    }

    Ok(None)
}

fn check_conf_file_exists(conf_file: &Path) -> anyhow::Result<Option<PathBuf>> {
    let exists = conf_file
        .try_exists()
        .with_context(|| format!("Could not read configuration file: {}", conf_file.display()))?;

    if exists {
        Ok(Some(conf_file.to_owned()))
    } else {
        bail!(format!(
            "configuration file does not exist: {}",
            conf_file.display()
        ))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::{env::set_current_dir, fs::create_dir};

    use log::TestLogger;
    use temp_dir::TempDir;

    use crate::util::test::create_tmp_child;

    #[test]
    fn load_sylver_state_ok() {
        let dir = TempDir::new().unwrap();

        create_dir(dir.path().join(".sylver")).unwrap();

        let subdir_path = dir.path().join("subdir");
        create_dir(&subdir_path).unwrap();
        set_current_dir(&subdir_path).unwrap();

        let state = SylverState::load(TestLogger::default()).unwrap();

        assert_eq!(
            state.locations,
            Locations {
                sylver_dir: Path::new("..").canonicalize().unwrap().join(".sylver"),
                repos: Path::new("..")
                    .canonicalize()
                    .unwrap()
                    .join(".sylver")
                    .join("dl")
                    .join("repos"),
                config_file: None
            }
        );
    }

    #[test]
    fn sylver_dir_location_present() {
        let dir = TempDir::new().unwrap();

        create_dir(dir.path().join(".sylver")).unwrap();

        let subdir_path = dir.path().join("subdir");
        create_dir(&subdir_path).unwrap();

        let sylver_dir = sylver_dir_location(&subdir_path);

        assert_eq!(sylver_dir, dir.path().join(".sylver"));
    }

    #[test]
    fn sylver_dir_location_missing() {
        let dir = TempDir::new().unwrap();
        let sylver_dir = sylver_dir_location(dir.path());

        assert_eq!(sylver_dir, dir.path().join(".sylver"));
    }

    #[test]
    fn config_location_missing() {
        let locations =
            Locations::from_sylver_dir(&Default::default(), PathBuf::from(".sylver")).unwrap();
        assert_eq!(locations.config_file, None);
    }

    #[test]
    fn config_location_override_non_existing_file() {
        let override_path = Path::new("config.yaml");

        let settings = SylverSettings {
            config_override: Some(override_path.to_owned()),
            ..Default::default()
        };

        let locations = Locations::from_sylver_dir(&settings, PathBuf::from(".sylver"));
        assert!(locations.is_err());
    }

    #[test]
    fn config_location_sylver_yml() {
        test_default_conf_file("yml");
    }

    #[test]
    fn config_location_sylver_yaml() {
        test_default_conf_file("yaml");
    }

    fn test_default_conf_file(ext: &str) {
        let filename = format!("sylver.{ext}");

        let tmp = TempDir::new().unwrap();
        let sylver_dir = tmp.path().join(".sylver");

        create_dir(&sylver_dir).unwrap();
        create_tmp_child(&tmp, &filename, "configuration_content").unwrap();

        let locations = Locations::from_sylver_dir(&Default::default(), sylver_dir).unwrap();

        assert_eq!(locations.config_file, Some(tmp.path().join(&filename)))
    }
}
