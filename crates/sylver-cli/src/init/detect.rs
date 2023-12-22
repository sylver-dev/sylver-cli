use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

use anyhow::{anyhow, bail, Context};
use log::Logger;
use semver::Version;

use sylver_core::{
    builtin_langs::{get_builtin_langs, get_detection_script, BuiltinLang},
    core::files_spec::FileSpec,
    dashboard::api::ReportLanguage,
    script::{ScriptEngine, ScriptError, ScriptValue},
    specs::{
        stem::location::{stem_location_from_str, StemLocation},
        stem::project::{ProjectLang, ProjectStem},
    },
    util::archive::{read_archive, ArchiveFile},
};

static SYLVER_VERSION: &str = env!("CARGO_PKG_VERSION");

static PROJECT_DETECTION_FUN: &str = "detect_projects";
static RULESET_CONFIG_FUN: &str = "configure";

#[derive(Debug, Clone)]
struct DetectedProject {
    file_spec: FileSpec,
}

#[derive(Debug, Clone)]
pub enum DetectableLanguage<S> {
    Builtin(BuiltinLang, S),
}

impl<S> DetectableLanguage<S> {
    pub fn name(&self) -> String {
        match self {
            DetectableLanguage::Builtin(lang, _) => lang.to_string(),
        }
    }

    pub fn script(&self) -> &S {
        match self {
            DetectableLanguage::Builtin(_, script) => script,
        }
    }

    fn build_project_stem(
        &self,
        detection_root: &Path,
        project: DetectedProject,
    ) -> anyhow::Result<ProjectStem> {
        let language = match self {
            DetectableLanguage::Builtin(lang, _) => ProjectLang::Builtin(*lang),
        };

        let root = project
            .file_spec
            .root
            .map(|r| keep_project_root_if_subdir(detection_root, &r))
            .transpose()?
            .flatten();

        Ok(ProjectStem {
            language,
            root,
            include: project.file_spec.include,
            exclude: project.file_spec.exclude,
            rulesets: vec![],
        })
    }
}

impl<E> From<&DetectableLanguage<E>> for ReportLanguage {
    fn from(lang: &DetectableLanguage<E>) -> Self {
        match lang {
            DetectableLanguage::Builtin(lang, _) => ReportLanguage::Builtin(*lang),
        }
    }
}

#[derive(Debug, Clone)]
pub struct DetectableRuleset<E: ScriptEngine> {
    pub identifier: String,
    pub author: String,
    pub name: String,
    pub version: Version,
    pub script: E::Script,
}

impl<E: ScriptEngine> DetectableRuleset<E> {
    fn from_archive_file(engine: &E, file: &ArchiveFile) -> anyhow::Result<DetectableRuleset<E>> {
        let Some(StemLocation::Registry {
            author,
            name,
            version: Some(v),
        }) = stem_location_from_str(&file.name)
        else {
            bail!("Invalid registry identifier: {}", file.name);
        };

        let script = engine
            .compile_function(
                &file.content,
                "ruleset_script".to_string(),
                RULESET_CONFIG_FUN.to_string(),
            )
            .context("Failed to compile ruleset configuration function")?;

        Ok(DetectableRuleset {
            author,
            name,
            script,
            version: v,
            identifier: file.name.clone(),
        })
    }
}

impl<E: ScriptEngine> From<&DetectableRuleset<E>> for StemLocation {
    fn from(value: &DetectableRuleset<E>) -> Self {
        StemLocation::Registry {
            author: value.author.clone(),
            name: value.name.clone(),
            version: Some(value.version.clone()),
        }
    }
}

#[derive(Debug)]
pub struct ProjectDetector<E: ScriptEngine> {
    client: reqwest::blocking::Client,
    backend_url: String,
    logger: Box<dyn Logger>,
    engine: E,
}

impl<E: ScriptEngine> ProjectDetector<E> {
    pub fn new(backend_url: String, logger: Box<dyn Logger>, engine: E) -> Self {
        Self {
            logger,
            engine,
            backend_url,
            client: reqwest::blocking::Client::new(),
        }
    }

    pub fn detect_builtin_lang_projects(&self, root: &Path) -> Vec<ProjectStem> {
        let langs = builtin_detectable_lang(&self.engine);
        self.detect_projects(root, &langs)
    }

    fn detect_projects(
        &self,
        root: &Path,
        languages: &[DetectableLanguage<E::Script>],
    ) -> Vec<ProjectStem> {
        self.logger.important("Detecting projects...");

        let mut projects = vec![];

        for language in languages {
            let language_name = language.name();

            match self.projects_for_lang(root, language) {
                Ok(ps) => {
                    for p in ps {
                        let dir_name = p
                            .root
                            .clone()
                            .unwrap_or_else(|| "current_directory".to_string());

                        self.logger
                            .info(&format!("Detected {language_name} project in {dir_name}"));

                        projects.push(p);
                    }
                }
                Err(e) => {
                    self.logger
                        .error(&format!("Failed to detect {language_name} projects: {e}"));
                }
            }
        }

        projects
    }

    fn projects_for_lang(
        &self,
        root: &Path,
        language: &DetectableLanguage<E::Script>,
    ) -> anyhow::Result<Vec<ProjectStem>> {
        let detection_result = self
            .engine
            .eval(
                language.script(),
                vec![root.to_string_lossy().to_string().into()],
            )
            .context(format!(
                "Failed to detect projects for language {}",
                language.name()
            ))?;

        let mut projects: Vec<ProjectStem> = projects_from_value(detection_result)?
            .into_iter()
            .map(|spec| language.build_project_stem(root, spec))
            .collect::<anyhow::Result<_>>()?;

        self.detect_rulesets(root, language, &mut projects);

        Ok(projects)
    }

    fn detect_rulesets(
        &self,
        root: &Path,
        language: &DetectableLanguage<E::Script>,
        projects: &mut Vec<ProjectStem>,
    ) {
        let compatible_rulesets = self.fetch_compatible_rulesets(language);

        for project in projects {
            let project_root = project
                .root
                .clone()
                .unwrap_or_else(|| root.to_string_lossy().to_string());

            for ruleset in &compatible_rulesets {
                if let Ok(ruleset_conf) = self
                    .engine
                    .eval(&ruleset.script, vec![project_root.clone().into()])
                {
                    if let Ok(true) = ruleset_conf.try_into() {
                        project.rulesets.push(ruleset.into());
                    }
                }
            }
        }
    }

    fn fetch_compatible_rulesets(
        &self,
        language: &DetectableLanguage<E::Script>,
    ) -> Vec<DetectableRuleset<E>> {
        let Ok(archive) = self.fetch_ruleset_archive(language) else {
            self.logger.error(&format!(
                "Failed to fetch ruleset archive for language: {}",
                language.name()
            ));
            return vec![];
        };

        let mut rulesets = vec![];
        for file in archive {
            match DetectableRuleset::from_archive_file(&self.engine, &file) {
                Ok(ruleset) => rulesets.push(ruleset),
                Err(e) => self
                    .logger
                    .error(&format!("Invalid ruleset file {}: {e:?}", file.name)),
            };
        }

        rulesets
    }

    fn fetch_ruleset_archive(
        &self,
        language: &DetectableLanguage<E::Script>,
    ) -> anyhow::Result<Vec<ArchiveFile>> {
        let url = format!("{}/registry/rulesets/detection_scripts", &self.backend_url);

        let response = self
            .client
            .get(url)
            .query(&[
                (
                    "language",
                    serde_json::to_string(&ReportLanguage::from(language)).unwrap(),
                ),
                ("sylver_version", SYLVER_VERSION.to_string()),
            ])
            .header("Content-Type", "application/octet-stream")
            .send()?;

        if response.status() != 200 {
            let response_text = response.text().unwrap_or_default();
            return Err(anyhow::anyhow!(
                "Failed to fetch ruleset archive: {}",
                response_text
            ));
        }

        let response_bytes = response.bytes().context("Failed to read response body")?;

        read_archive(&response_bytes)
    }
}

fn builtin_detectable_lang<E: ScriptEngine>(engine: &E) -> Vec<DetectableLanguage<E::Script>> {
    get_builtin_langs()
        .into_iter()
        .map(|lang| {
            let script = engine
                .compile_function(
                    get_detection_script(lang),
                    "builtin".to_string(),
                    PROJECT_DETECTION_FUN.to_string(),
                )
                .unwrap();
            DetectableLanguage::Builtin(lang, script)
        })
        .collect()
}

fn projects_from_value(value: ScriptValue) -> anyhow::Result<Vec<DetectedProject>> {
    let specs: Vec<ScriptValue> = value
        .try_into()
        .context("project detection script should return a list of file specs")?;

    specs.into_iter().map(project_from_value).collect()
}

fn project_from_value(value: ScriptValue) -> anyhow::Result<DetectedProject> {
    let spec: BTreeMap<String, ScriptValue> =
        value.try_into().context("project spec should be a dict")?;

    let root_value = spec.get("root").cloned();

    let include_value = spec
        .get("include")
        .cloned()
        .ok_or_else(|| anyhow!("Missing 'include' key in project spec"))?;

    let exclude_value = spec
        .get("exclude")
        .cloned()
        .unwrap_or_else(|| ScriptValue::List(vec![]));

    Ok(DetectedProject {
        file_spec: FileSpec {
            root: root_value
                .map(|r| r.try_into())
                .transpose()
                .context("root should be a string")?,
            include: as_str_list(include_value).context("invalid 'include' field for file spec")?,
            exclude: as_str_list(exclude_value).context("invalid 'exlude' field for file spec")?,
        },
    })
}

fn keep_project_root_if_subdir(
    detection_root: &Path,
    root: &str,
) -> anyhow::Result<Option<String>> {
    let root_path = PathBuf::from(root);

    let project_root_abs = if root_path.is_absolute() {
        root_path
    } else {
        detection_root.join(root_path)
    }
    .canonicalize()
    .context(format!("invalid project root: {root}"))?;

    if project_root_abs != detection_root.canonicalize().unwrap() {
        Ok(Some(root.to_string()))
    } else {
        Ok(None)
    }
}

fn as_str_list(value: ScriptValue) -> Result<Vec<String>, ScriptError> {
    let values: Vec<ScriptValue> = value.try_into()?;
    values.into_iter().map(TryInto::try_into).collect()
}
