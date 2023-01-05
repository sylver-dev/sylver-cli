use std::collections::HashMap;

use anyhow::{bail, Context};

use sylver_core::dashboard::api::ReportDTO;
use sylver_core::{
    core::source::SourceTree,
    dashboard::api::{NewDiagnosticDTO, NewReportDTO, ReportCustomLanguage, ReportLanguage},
    land::{cmds::RuleResult, ruleset::Rule, LandSpecId},
    query::SylvaNode,
    specs::{
        loader::{Loader, SylverLoader},
        stem::project::ProjectLang,
    },
    tree::info::{raw::RawTreeInfo, TreeInfo},
    util::{fs::path_to_string, git::GitClient, iter::group_by},
};

use crate::{check::CheckLandData, cli::CheckCmd};

pub struct ReportUploader<'s> {
    loader: &'s SylverLoader,
    cmd: &'s CheckCmd,
    check_data: &'s CheckLandData,
    client: reqwest::blocking::Client,
}

impl<'s> ReportUploader<'s> {
    pub fn new(loader: &'s SylverLoader, cmd: &'s CheckCmd, check_data: &'s CheckLandData) -> Self {
        let client = reqwest::blocking::Client::new();

        Self {
            loader,
            cmd,
            check_data,
            client,
        }
    }

    pub fn upload(&self, results: &[RuleResult]) {
        let res_per_lang: HashMap<LandSpecId, Vec<RuleResult>> =
            group_by(results.iter().cloned(), |r: &RuleResult| {
                self.check_data.land.sylva_spec_id(r.node.sylva)
            });

        std::thread::scope(|s| {
            for (spec_id, results) in res_per_lang {
                s.spawn(
                    move || match self.upload_report_for_lang(spec_id, results) {
                        Ok(_) => (),
                        Err(e) => eprintln!("failed to upload report: {e:?}"),
                    },
                );
            }
        });
    }

    pub fn upload_report_for_lang(
        &self,
        lang: LandSpecId,
        results: Vec<RuleResult>,
    ) -> anyhow::Result<()> {
        let report = self.upload_report(lang)?;
        self.upload_diagnostics(&report, results)?;
        Ok(())
    }

    fn upload_diagnostics(
        &self,
        report: &ReportDTO,
        results: Vec<RuleResult>,
    ) -> anyhow::Result<()> {
        let diagnostics: Vec<NewDiagnosticDTO> = results
            .iter()
            .map(|r| self.build_diagnostic(report, &r))
            .collect();

        let Some(token) = &self.cmd.token else { bail!("Missing Sylver token") };

        self.client
            .post(format!(
                "{}/reports/{}/diagnostics",
                &self.cmd.upload_url, report.id
            ))
            .body(serde_json::to_string(&diagnostics).unwrap())
            .header("Content-Type", "application/json")
            .header("user_token", token.as_str())
            .send()
            .context("failed to upload diagnostics")?;

        Ok(())
    }

    fn build_diagnostic(&self, report: &ReportDTO, r: &&RuleResult) -> NewDiagnosticDTO {
        let info = self.get_tree_info(r.node);

        NewDiagnosticDTO {
            report_id: report.id,
            rule_set: self.check_data.rulesets.get(&r.ruleset).unwrap().clone(),
            rule: r.rule_id.to_string(),
            description: self.get_rule(r).message.clone(),
            file: path_to_string(self.get_tree(r.node).source.path()),
            position: info.node_pos(r.node.node).into(),
        }
    }

    fn get_tree_info(&self, n: SylvaNode) -> RawTreeInfo {
        RawTreeInfo::new(
            self.get_tree(n),
            &self.check_data.land.sylva_spec(n.sylva).syntax,
        )
    }

    fn get_tree(&self, n: SylvaNode) -> &SourceTree {
        self.check_data.land.sylva_node_tree(n)
    }

    fn get_rule(&self, r: &RuleResult) -> &Rule {
        self.check_data
            .land
            .ruleset(r.ruleset)
            .get_rule(&r.rule_id)
            .unwrap()
    }

    pub fn upload_report(&self, lang: LandSpecId) -> anyhow::Result<ReportDTO> {
        let report_data = self.build_report(lang)?;

        let Some(token) = &self.cmd.token else { bail!("Missing Sylver token") };

        let report_str = self
            .client
            .post(format!("{}/reports", &self.cmd.upload_url))
            .body(serde_json::to_string(&report_data).unwrap())
            .header("Content-Type", "application/json")
            .header("user_token", token.as_str())
            .send()
            .context("failed to create report")?
            .text()?;

        let report = serde_json::from_str::<ReportDTO>(&report_str).unwrap();

        Ok(report)
    }

    pub fn build_report(&self, lang: LandSpecId) -> anyhow::Result<NewReportDTO> {
        let commit = GitClient::current_commit()?;
        let branch = GitClient::current_branch()?;

        let project_language = self.check_data.langs.get(&lang).unwrap();

        let language = match project_language {
            ProjectLang::Builtin(b) => ReportLanguage::Builtin(*b),
            ProjectLang::Custom(stem) => ReportLanguage::Custom(ReportCustomLanguage {
                name: self.loader.langs.id(stem).unwrap(),
                stem: stem.clone(),
            }),
        };

        Ok(NewReportDTO {
            commit,
            branch,
            language,
        })
    }
}
