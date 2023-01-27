use std::{ffi::OsStr, fs::read_to_string, path::Path, path::PathBuf, sync::Arc};

use anyhow::{anyhow, Context};
use log::Logger;
use semver::Version;
use serde::de::DeserializeOwned;

use crate::{
    api::{ApiClient, RegistryItemKind},
    core::{
        files_spec::{FileSpec, FileSpecLoader, FsFileSpecLoader},
        source::Source,
        spec::{spec_from_file, Spec},
    },
    specs::stem::{
        language::LanguageStem, location::StemLocation, project::ProjectConfigStem,
        ruleset::RuleSetStem,
    },
    state::SylverState,
    util::git::GitClient,
};

#[derive(Debug, Clone)]
pub struct SylverLoader<
    F: FileSpecLoader = FsFileSpecLoader,
    R: LocationLoader<RuleSetStem> = FullLocationLoader<RulesetStemLoader>,
    C: PathLoader<Output = ProjectConfigStem> = DefaultPathLoader<ProjectConfigStem>,
    S: LocationLoader<Spec> = FullLocationLoader<LanguageStemLoader>,
> {
    files: F,
    rulesets: R,
    projects: C,
    pub langs: S,
}

impl<
        F: FileSpecLoader,
        R: LocationLoader<RuleSetStem>,
        P: PathLoader<Output = ProjectConfigStem>,
        S: LocationLoader<Spec>,
    > SylverLoader<F, R, P, S>
{
    pub fn new(files: F, rulesets: R, projects: P, langs: S) -> Self {
        SylverLoader {
            files,
            rulesets,
            projects,
            langs,
        }
    }

    pub fn load_file_spec(&self, path: &FileSpec) -> anyhow::Result<Vec<Source>> {
        self.files.load(path)
    }

    pub fn load_language_spec(&self, location: &StemLocation) -> anyhow::Result<Spec> {
        self.langs.load(location)
    }

    pub fn load_ruleset(&self, path: &StemLocation) -> anyhow::Result<RuleSetStem> {
        self.rulesets.load(path)
    }

    pub fn load_config(&self, path: &Path) -> anyhow::Result<ProjectConfigStem> {
        self.projects.load(path)
    }
}

impl SylverLoader {
    pub fn from_state(state: Arc<SylverState>) -> SylverLoader {
        SylverLoader::new(
            FsFileSpecLoader::default(),
            FullLocationLoader::from_state(state.clone()),
            DefaultPathLoader::new("config".to_string()),
            FullLocationLoader::from_state(state),
        )
    }
}

pub trait PathLoader {
    type Output;
    fn load(&self, path: &Path) -> anyhow::Result<Self::Output>;
    fn id(&self, path: &Path) -> anyhow::Result<String>;
    fn artefact_type(&self) -> &str;
}

#[derive(Debug, Clone)]
pub struct DefaultPathLoader<T> {
    _ph: std::marker::PhantomData<T>,
    artefact_type: String,
}

impl<T: DeserializeOwned> DefaultPathLoader<T> {
    pub fn new(artefact_type: String) -> DefaultPathLoader<T> {
        DefaultPathLoader {
            _ph: std::marker::PhantomData::default(),
            artefact_type,
        }
    }

    pub fn validate_extension(path: &Path) -> anyhow::Result<()> {
        match path.extension() {
            Some(ext) if ext == OsStr::new("yml") || ext == OsStr::new("yaml") => Ok(()),
            Some(ext) => Err(anyhow!("unsupported extension: {}", ext.to_string_lossy())),
            None => Err(anyhow!(
                "missing extension for stem file: {}",
                path.display()
            )),
        }
    }

    fn load_from_path<U: DeserializeOwned>(&self, path: &Path) -> anyhow::Result<U> {
        let stem_str = read_to_string(path)
            .with_context(|| format!("cannot read stem file: {}", path.display()))?;

        serde_yaml::from_str(&stem_str).map_err(|e| {
            let prefix = format!("Invalid stem: {}", path.display());

            let msg = match e.location() {
                Some(l) => {
                    let line = l.line();
                    let column = l.column();
                    format!("{prefix}. Error at line {line}, column {column}.",)
                }
                None => prefix,
            };

            anyhow!(msg)
        })
    }
}

impl<T: DeserializeOwned> PathLoader for DefaultPathLoader<T> {
    type Output = T;

    fn load(&self, path: &Path) -> anyhow::Result<T> {
        Self::validate_extension(path)?;
        self.load_from_path(path)
    }

    fn id(&self, path: &Path) -> anyhow::Result<String> {
        Self::validate_extension(path)?;

        let val: serde_yaml::Value = self.load_from_path(path)?;
        val.get("id")
            .and_then(|v| v.as_str())
            .map(|s| s.to_string())
            .ok_or_else(|| anyhow!("missing id field in {}", path.display()))
    }

    fn artefact_type(&self) -> &str {
        &self.artefact_type
    }
}

pub trait Loader<T> {
    type Output;

    fn load(&self, res: &T) -> anyhow::Result<Self::Output>;

    fn id(&self, res: &T) -> anyhow::Result<String>;
}

#[derive(Debug, Clone)]
pub struct RegistryLoader {
    state: Arc<SylverState>,
    item_kind: RegistryItemKind,
    client: ApiClient,
}

impl RegistryLoader {
    pub fn new(state: Arc<SylverState>, client: ApiClient) -> RegistryLoader {
        RegistryLoader {
            state,
            client,
            item_kind: RegistryItemKind::RuleSet,
        }
    }

    fn item_file_name(&self) -> &str {
        match self.item_kind {
            RegistryItemKind::RuleSet => "ruleset.yaml",
        }
    }

    fn load(&self, author: &str, name: &str, version: Option<&Version>) -> anyhow::Result<PathBuf> {
        let version_suffix = match version {
            Some(v) => format!(":{v}"),
            None => "".to_string(),
        };

        let path = self
            .state
            .locations
            .registry_artefacts
            .join(format!("@{author}"))
            .join(format!("{name}{version_suffix}"))
            .join(self.item_file_name());

        if !path.exists() || !path.is_file() {
            let artefact_id = StemLocation::Registry {
                name: name.to_string(),
                author: author.to_string(),
                version: version.cloned(),
            }
            .to_string();

            let message = format!("Downloading {artefact_id} from registry");

            let _ = self.state.logger.scoped(&message, None);

            self.client.fetch_from_registry(
                &self.state.locations.registry_artefacts,
                self.item_kind,
                author,
                name,
                version,
            )?;
        }

        Ok(path)
    }
}

pub trait LocationLoader<O>: Loader<StemLocation, Output = O> {}

#[derive(Debug, Clone)]
pub struct FullLocationLoader<Load: PathLoader> {
    state: Arc<SylverState>,
    registry_loader: RegistryLoader,
    git_client: GitClient,
    loader: Load,
}

impl<L: PathLoader> FullLocationLoader<L> {
    pub fn new(
        state: Arc<SylverState>,
        registry_loader: RegistryLoader,
        git_client: GitClient,
        loader: L,
    ) -> FullLocationLoader<L> {
        FullLocationLoader {
            state,
            registry_loader,
            git_client,
            loader,
        }
    }
}

impl<L: PathLoader + Default> FullLocationLoader<L> {
    pub fn from_state(state: Arc<SylverState>) -> Self {
        Self::new(
            state.clone(),
            RegistryLoader::new(state.clone(), ApiClient::from_state(state)),
            GitClient::default(),
            L::default(),
        )
    }
}

impl<L: PathLoader> FullLocationLoader<L> {
    fn loaded_location_path(&self, location: &StemLocation) -> anyhow::Result<PathBuf> {
        match location {
            StemLocation::Local(p) => Ok(p.clone()),
            StemLocation::Registry {
                author,
                name,
                version,
            } => self.registry_loader.load(author, name, version.as_ref()),
            StemLocation::Git { repo, file, .. } => self
                .git_client
                .clone_repo(
                    &self.state.logger,
                    self.loader.artefact_type(),
                    repo,
                    &self.state.locations.repos,
                )
                .map(|p| p.join(file)),
        }
    }
}

impl<L: PathLoader> Loader<StemLocation> for FullLocationLoader<L> {
    type Output = L::Output;

    fn load(&self, res: &StemLocation) -> anyhow::Result<Self::Output> {
        let path = self.loaded_location_path(res)?;
        self.loader.load(&path)
    }

    fn id(&self, res: &StemLocation) -> anyhow::Result<String> {
        let path = self.loaded_location_path(res)?;
        path.file_name()
            .map(|n| n.to_string_lossy().to_string())
            .ok_or_else(|| anyhow!("missing file name for stem file: {}", path.display()))
    }
}

impl<L: PathLoader> LocationLoader<L::Output> for FullLocationLoader<L> {}

#[derive(Debug)]
pub struct LanguageStemLoader {
    default_loader: DefaultPathLoader<LanguageStem>,
}

impl LanguageStemLoader {
    pub fn is_syl_fil(&self, path: &Path) -> bool {
        matches!(path.extension(), Some(ext) if ext == OsStr::new("syl"))
    }

    pub fn language_name(&self, path: &Path) -> anyhow::Result<String> {
        if self.is_syl_fil(path) {
            Ok(path.file_name().unwrap().to_string_lossy().to_string())
        } else {
            self.default_loader.load(path).map(|stem| stem.id)
        }
    }
}

impl Default for LanguageStemLoader {
    fn default() -> Self {
        LanguageStemLoader {
            default_loader: DefaultPathLoader::new("language spec".to_string()),
        }
    }
}

impl PathLoader for LanguageStemLoader {
    type Output = Spec;

    fn load(&self, path: &Path) -> anyhow::Result<Spec> {
        if self.is_syl_fil(path) {
            spec_from_file(path)
        } else {
            self.default_loader.load(path).and_then(|stem| {
                let spec_path = path.with_file_name(stem.spec);
                spec_from_file(&spec_path)
            })
        }
    }

    fn id(&self, path: &Path) -> anyhow::Result<String> {
        self.language_name(path)
    }

    fn artefact_type(&self) -> &str {
        self.default_loader.artefact_type()
    }
}

#[derive(Debug)]
pub struct RulesetStemLoader {
    loader: DefaultPathLoader<RuleSetStem>,
}

impl PathLoader for RulesetStemLoader {
    type Output = RuleSetStem;

    fn load(&self, path: &Path) -> anyhow::Result<Self::Output> {
        self.loader.load(path)
    }

    fn id(&self, path: &Path) -> anyhow::Result<String> {
        self.loader.id(path)
    }

    fn artefact_type(&self) -> &str {
        self.loader.artefact_type()
    }
}

impl Default for RulesetStemLoader {
    fn default() -> Self {
        RulesetStemLoader {
            loader: DefaultPathLoader::new("ruleset".to_string()),
        }
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;
    use temp_dir::TempDir;

    use crate::util::test::create_tmp_child;

    use super::*;

    #[test]
    fn spec_from_syl() {
        let spec_str = "term HELLO = 'hello'";
        let dir = TempDir::new().unwrap();
        let spec_path = create_tmp_child(&dir, "spec.syl", spec_str).unwrap();

        let loaded = LanguageStemLoader::default().load(&spec_path).unwrap();

        assert_eq!(loaded, spec_from_file(&spec_path).unwrap());
    }

    #[test]
    fn spec_from_yaml_stem() {
        let spec_str = "term HELLO = 'hello'";
        let stem_str = indoc!(
            "
            id: myLanguage
            spec: spec.syl
        "
        );
        let dir = TempDir::new().unwrap();
        let spec_path = create_tmp_child(&dir, "spec.syl", spec_str).unwrap();

        let stem_path = create_tmp_child(&dir, "spec.yml", stem_str).unwrap();

        let loaded = LanguageStemLoader::default().load(&stem_path).unwrap();

        assert_eq!(loaded, spec_from_file(&spec_path).unwrap());
    }
}
