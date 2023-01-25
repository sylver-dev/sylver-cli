use std::{collections::HashSet, path::Path};

use anyhow::Context;

use super::source::{source_from_file, Source};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct FileSpec {
    pub root: Option<String>,
    pub include: Vec<String>,
    pub exclude: Vec<String>,
}

pub trait FileSpecLoader {
    fn load(&self, spec: &FileSpec) -> anyhow::Result<Vec<Source>>;
}

#[derive(Default, Clone, Eq, PartialEq, Hash)]
pub struct FsFileSpecLoader {}

impl FsFileSpecLoader {
    fn sources_from_globs(
        &self,
        root: Option<&String>,
        globs: &[String],
    ) -> anyhow::Result<HashSet<Source>> {
        let mut sources = HashSet::new();
        for glob in globs {
            let glob_in_root = if let Some(r) = root {
                Path::new(r).join(glob).to_string_lossy().to_string()
            } else {
                glob.clone()
            };

            sources.extend(sources_from_glob(&glob_in_root)?);
        }
        Ok(sources)
    }
}

impl FileSpecLoader for FsFileSpecLoader {
    fn load(&self, spec: &FileSpec) -> anyhow::Result<Vec<Source>> {
        Ok(self
            .sources_from_globs(spec.root.as_ref(), &spec.include)?
            .difference(&self.sources_from_globs(spec.root.as_ref(), &spec.exclude)?)
            .cloned()
            .collect())
    }
}

fn sources_from_glob(pattern: &str) -> anyhow::Result<Vec<Source>> {
    glob::glob(pattern)
        .context("Failed to parse glob pattern")?
        .collect::<Result<Vec<_>, _>>()
        .context("Failed to evaluate glob")?
        .iter()
        .map(|p| source_from_file(p))
        .collect::<Result<_, _>>()
        .context("Failed to build source")
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use maplit::hashset;
    use temp_dir::TempDir;

    use super::*;
    use crate::util::test::create_tmp_child;

    #[test]
    fn fs_file_spec_handles_root_directory() {
        let d = TempDir::new().unwrap();

        std::fs::create_dir(d.path().join("root")).unwrap();
        let match1 = create_tmp_child(&d, "root/match1.ok", "content1").unwrap();
        let match2 = create_tmp_child(&d, "root/match2.ok", "content2").unwrap();
        create_tmp_child(&d, "match.ok", "nomatch_content").unwrap();

        let spec = FileSpec {
            root: Some(d.path().join("root").to_string_lossy().to_string()),
            include: vec!["*.ok".to_string()],
            exclude: vec![],
        };

        let loaded = FsFileSpecLoader::default().load(&spec).unwrap();

        assert_eq!(
            loaded.into_iter().collect::<HashSet<Source>>(),
            hashset![
                source_from_file(&match1).unwrap(),
                source_from_file(&match2).unwrap(),
            ]
        )
    }

    #[test]
    fn fs_file_spec_ok() {
        let d = TempDir::new().unwrap();

        let match1 = create_tmp_child(&d, "match1.ok", "content1").unwrap();
        let match2 = create_tmp_child(&d, "match2.ok", "content2").unwrap();
        let _ = create_tmp_child(&d, "nomatch.other", "nomatch_content").unwrap();

        let spec = FileSpec {
            root: None,
            include: vec![format!("{}/*.ok", d.path().display())],
            exclude: vec![],
        };

        let loaded = FsFileSpecLoader::default().load(&spec).unwrap();

        assert_eq!(
            loaded.into_iter().collect::<HashSet<Source>>(),
            hashset![
                source_from_file(&match1).unwrap(),
                source_from_file(&match2).unwrap(),
            ]
        )
    }

    #[test]
    fn fs_file_spec_with_exclude() {
        let d = TempDir::new().unwrap();

        let match1 = create_tmp_child(&d, "match1.ok", "content1").unwrap();
        let match2 = create_tmp_child(&d, "match2.ok", "content2").unwrap();
        let _ = create_tmp_child(&d, "excluded_match.ok", "content3").unwrap();
        let _ = create_tmp_child(&d, "nomatch.other", "nomatch_content").unwrap();

        let spec = FileSpec {
            root: None,
            include: vec![format!("{}/*.ok", d.path().display())],
            exclude: vec![format!("{}/excluded*", d.path().display())],
        };

        let loaded = FsFileSpecLoader::default().load(&spec).unwrap();

        assert_eq!(
            loaded.into_iter().collect::<HashSet<Source>>(),
            hashset![
                source_from_file(&match1).unwrap(),
                source_from_file(&match2).unwrap(),
            ]
        )
    }
}
