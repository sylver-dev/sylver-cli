use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

use anyhow::{anyhow, Context};
use log::Logger;
use sylver_core::{
    builtin_langs::{get_builtin_langs, get_detection_script, BuiltinLang},
    core::files_spec::FileSpec,
    specs::stem::project::{ProjectLang, ProjectStem},
};
use sylver_script::{ScriptEngine, ScriptError, ScriptValue};

static PROJECT_DETECTION_FUN: &str = "detect_project";

#[derive(Debug, Clone)]
struct DetectedProject {
    root: Option<String>,
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

pub fn detect_builtin_lang_projects<E: ScriptEngine>(
    engine: &E,
    logger: &dyn Logger,
    root: &Path,
) -> anyhow::Result<Vec<ProjectStem>> {
    let langs = builtin_detectable_lang(engine);
    detect_projects(engine, logger, root, &langs)
}

fn builtin_detectable_lang<E: ScriptEngine>(engine: &E) -> Vec<DetectableLanguage<E::Script>> {
    get_builtin_langs()
        .into_iter()
        .map(|lang| {
            let script = engine
                .compile_function(get_detection_script(lang), "builtin", PROJECT_DETECTION_FUN)
                .unwrap();
            DetectableLanguage::Builtin(lang, script)
        })
        .collect()
}

fn detect_projects<E: ScriptEngine>(
    engine: &E,
    logger: &dyn Logger,
    root: &Path,
    languages: &[DetectableLanguage<E::Script>],
) -> anyhow::Result<Vec<ProjectStem>> {
    logger.important("Detecting projects...");

    let mut projects = vec![];

    for language in languages {
        let language_name = language.name();
        for p in projects_for_lang(engine, root, language)? {
            logger.info(&format!(
                "Detected {language_name} project in {}",
                p.root
                    .clone()
                    .unwrap_or_else(|| "current directory".to_string())
            ));
            projects.push(p);
        }
    }

    Ok(projects)
}

fn projects_for_lang<E: ScriptEngine>(
    engine: &E,
    root: &Path,
    language: &DetectableLanguage<E::Script>,
) -> anyhow::Result<Vec<ProjectStem>> {
    let detection_result = engine
        .eval(
            language.script(),
            vec![root.to_string_lossy().to_string().into()],
        )
        .context(format!(
            "Failed to detect projects for language {}",
            language.name()
        ))?;

    let projects: Vec<ProjectStem> = projects_from_value(detection_result)?
        .into_iter()
        .map(|spec| language.build_project_stem(root, spec))
        .collect::<anyhow::Result<_>>()?;

    Ok(projects)
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
        root: root_value
            .map(|r| r.try_into())
            .transpose()
            .context("root should be a string")?,
        file_spec: FileSpec {
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
