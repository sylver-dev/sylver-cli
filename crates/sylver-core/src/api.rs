use std::{path::Path, sync::Arc};

use anyhow::Context;
use semver::Version;

use crate::{state::SylverState, util::archive::read_archive};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegistryItemKind {
    RuleSet,
}

#[derive(Debug, Clone)]
pub struct ApiClient {
    backend_url: String,
    client: reqwest::blocking::Client,
}

impl ApiClient {
    pub fn from_state(state: Arc<SylverState>) -> ApiClient {
        ApiClient::new(
            state.settings.backend_url.clone(),
            reqwest::blocking::Client::new(),
        )
    }

    pub fn new(backend_url: String, client: reqwest::blocking::Client) -> Self {
        Self {
            backend_url,
            client,
        }
    }

    pub fn fetch_from_registry(
        &self,
        download_dir: &Path,
        kind: RegistryItemKind,
        author: &str,
        name: &str,
        version: Option<&Version>,
    ) -> anyhow::Result<()> {
        let archive = self.fetch_registry_archive(kind, author, name, version)?;

        for archive_file in read_archive(&archive)? {
            let path = archive_file
                .name
                .split('/')
                .fold(download_dir.to_path_buf(), |path, component| {
                    path.join(component)
                });

            std::fs::create_dir_all(path.parent().unwrap()).context(format!(
                "failed to create directory {}",
                path.to_string_lossy()
            ))?;

            std::fs::write(&path, archive_file.content)
                .context(format!("failed to write file {}", path.to_string_lossy()))?;
        }

        Ok(())
    }

    fn fetch_registry_archive(
        &self,
        kind: RegistryItemKind,
        author: &str,
        name: &str,
        version: Option<&Version>,
    ) -> anyhow::Result<Vec<u8>> {
        let url = match kind {
            RegistryItemKind::RuleSet => format!("{}/registry/rulesets", &self.backend_url),
        };

        let mut params = vec![("author", author.to_string()), ("name", name.to_string())];

        if let Some(version) = version {
            params.push(("version", version.to_string()));
        }

        let response = self
            .client
            .get(url)
            .query(&params)
            .send()
            .context("Failed to fetch ruleset from registry")?;

        if !response.status().is_success() {
            return Err(anyhow::anyhow!(
                "Failed to fetch ruleset from registry: {}",
                response.text().unwrap()
            ));
        }

        let ruleset_bytes = response
            .bytes()
            .context("Failed to read ruleset from registry")?;

        Ok(ruleset_bytes.to_vec())
    }
}
