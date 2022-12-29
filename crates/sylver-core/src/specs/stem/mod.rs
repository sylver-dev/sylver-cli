use serde::{Deserialize, Serialize};

use crate::specs::stem::{language::LanguageStem, ruleset::RuleSetStem};

pub mod language;
pub mod location;
pub mod project;
pub mod ruleset;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
pub struct Stem<D> {
    #[serde(flatten)]
    pub data: D,
    pub description: Option<String>,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum StemData {
    #[serde(rename = "language")]
    Language(language::LanguageStem),
    #[serde(rename = "ruleset")]
    RuleSet(ruleset::RuleSetStem),
    #[serde(rename = "project")]
    Project(project::ProjectConfigStem),
}

pub fn parse_language_stem(txt: &str) -> Result<Stem<LanguageStem>, serde_yaml::Error> {
    serde_yaml::from_str(txt)
}

pub fn parse_ruleset_stem(txt: &str) -> Result<Stem<RuleSetStem>, serde_yaml::Error> {
    serde_yaml::from_str(txt)
}

#[cfg(test)]
mod test {
    use std::path::Path;

    use indoc::indoc;

    use crate::{
        builtin_langs::BuiltinLang,
        land::ruleset::RuleSeverity,
        specs::stem::project::{ProjectConfigStem, ProjectLang, ProjectStem},
    };

    use super::{
        language::LanguageStem,
        location::StemLocation,
        ruleset::{RuleSetStem, RuleStem},
        Stem, StemData,
    };

    #[test]
    fn language_stem() {
        let stem = read_stem(indoc!(
            "
            kind: language
            id: myLanguage
            spec: dir/language.syl
            description: This is the best language ever !
        "
        ))
        .unwrap();

        assert_eq!(
            stem,
            Stem {
                description: Some("This is the best language ever !".to_string()),
                data: StemData::Language(LanguageStem {
                    id: "myLanguage".to_string(),
                    spec: "dir/language.syl".into(),
                }),
            }
        );
    }

    #[test]
    fn ruleset_stem() {
        let stem = read_stem(indoc!(
            "
            kind: ruleset
            id: myRuleSet
            
            language: dir/language.syl
            
            rules:
                - id: rule1Id
                  message: Rule 1 message
                  query: match NodeKind1
                  severity: error 

                - id: rule2Id
                  message: Rule 2 message
                  query: match NodeKind2
                  severity: warning
                  note: More info
        "
        ))
        .unwrap();

        assert_eq!(
            stem,
            Stem {
                description: None,
                data: StemData::RuleSet(RuleSetStem {
                    id: "myRuleSet".to_string(),
                    language: ProjectLang::Custom(StemLocation::local("dir/language.syl")),
                    rules: vec![
                        RuleStem {
                            id: "rule1Id".to_string(),
                            message: "Rule 1 message".to_string(),
                            query: "match NodeKind1".to_string(),
                            severity: RuleSeverity::Error,
                            note: None,
                        },
                        RuleStem {
                            id: "rule2Id".to_string(),
                            message: "Rule 2 message".to_string(),
                            query: "match NodeKind2".to_string(),
                            severity: RuleSeverity::Warning,
                            note: Some("More info".to_string()),
                        },
                    ],
                }),
            }
        );
    }

    #[test]
    fn git_ruleset_stem() {
        let stem: Stem<RuleSetStem> = read_stem(indoc!(
            "
            kind: ruleset
            id: myRuleSet
            
            language:
                repo: https://github.com/torvalds/linux.git
                file: language.yml
            
            rules:
                - id: rule1Id
                  message: Rule 1 message
                  query: match NodeKind1
                  severity: error 
        "
        ))
        .unwrap();

        assert_eq!(
            stem.data.language,
            ProjectLang::Custom(StemLocation::Git {
                repo: "https://github.com/torvalds/linux.git".to_string(),
                file: Path::new("language.yml").to_owned(),
                metadata: None,
            })
        )
    }

    #[test]
    fn inline_git_ruleset_stem() {
        let stem: Stem<RuleSetStem> = read_stem(indoc!(
            "
            kind: ruleset
            id: myRuleSet

            language: https://github.com/torvalds/linux.git#language.yml
            
            rules:
                - id: rule1Id
                  message: Rule 1 message
                  query: match NodeKind1
                  severity: error
        "
        ))
        .unwrap();

        assert_eq!(
            stem.data.language,
            ProjectLang::Custom(StemLocation::Git {
                repo: "https://github.com/torvalds/linux.git".to_string(),
                file: Path::new("language.yml").to_owned(),
                metadata: None,
            })
        )
    }

    #[test]
    fn flat_project_default_language() {
        let stem: Stem<ProjectConfigStem> = read_stem(indoc!(
            "
            language: python
            include:
                - '*.py'
        "
        ))
        .unwrap();

        assert_eq!(
            stem,
            Stem {
                data: ProjectConfigStem::Flat(ProjectStem {
                    language: ProjectLang::Builtin(BuiltinLang::Python),
                    include: vec!["*.py".to_string()],
                    rulesets: vec![],
                }),
                description: None,
            }
        )
    }

    #[test]
    fn flat_project_stem() {
        let stem: Stem<ProjectConfigStem> = read_stem(indoc!(
            "
            language: lang.syl
            include:
                - '*.ext'
        "
        ))
        .unwrap();

        assert_eq!(
            stem,
            Stem {
                data: ProjectConfigStem::Flat(ProjectStem {
                    language: ProjectLang::Custom(StemLocation::local("lang.syl")),
                    include: vec!["*.ext".to_string()],
                    rulesets: vec![],
                }),
                description: None,
            }
        )
    }

    #[test]
    fn nested_projects_stem() {
        let stem: Stem<ProjectConfigStem> = read_stem(indoc!(
            "
            projects:
                - language: javascript.yml
                  rulesets: [ 'default.yml' ]
                  include:
                    - 'src/**/*.js'

                - language: golang.yml
                  include:
                    - 'src/**/*.go'
        "
        ))
        .unwrap();

        assert_eq!(
            stem,
            Stem {
                data: ProjectConfigStem::Nested {
                    projects: vec![
                        ProjectStem {
                            language: ProjectLang::Custom(StemLocation::Local(
                                "javascript.yml".into()
                            )),
                            rulesets: vec![StemLocation::Local("default.yml".into())],
                            include: vec!["src/**/*.js".to_string()],
                        },
                        ProjectStem {
                            language: ProjectLang::Custom(StemLocation::Local("golang.yml".into())),
                            rulesets: vec![],
                            include: vec!["src/**/*.go".to_string()],
                        },
                    ]
                },
                description: None,
            }
        )
    }

    fn read_stem<'de, D: serde::Deserialize<'de>>(
        stem: &'de str,
    ) -> Result<Stem<D>, serde_yaml::Error> {
        serde_yaml::from_str(stem)
    }
}
