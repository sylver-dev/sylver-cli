use std::{
    cmp::Ordering,
    collections::HashMap,
    path::{Path, PathBuf},
};

use id_vec::{Id, IdVec};
use rayon::prelude::*;

use crate::{
    builtin_langs::parser::BuiltinParserRunner,
    core::{
        source::{Source, SourceTree},
        spec::Spec,
    },
    id_type,
    parsing::parser_runner::{ParserRunner, ParsingResult},
    report::Report,
    tree::NodeId,
};

id_type! { SylvaId: Sylva }

id_type! { SylvaTreeId: SylvaTree }

#[derive(Debug, Clone)]
pub enum SylvaParser<'s> {
    Custom(ParserRunner<'s>),
    Builtin(BuiltinParserRunner<'s>),
}

impl<'s> SylvaParser<'s> {
    fn run(&self, source: Source) -> ParsingResult {
        match self {
            SylvaParser::Custom(p) => p.run_once(source),
            SylvaParser::Builtin(p) => p.run(source),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct SylvaTree {
    pub tree: SourceTree,
    pub reports: Vec<Report>,
    pub path: PathBuf,
}

impl SylvaTree {
    pub fn nodes(&'_ self) -> impl '_ + Iterator<Item = NodeId> {
        self.tree.tree.bottom_up_node_ids()
    }
}

/// Parse forest.
#[derive(Clone, Debug)]
pub struct Sylva {
    trees: IdVec<SylvaTree>,
    tree_paths: HashMap<PathBuf, SylvaTreeId>,
}

impl Sylva {
    pub fn new(results: HashMap<PathBuf, ParsingResult>) -> Sylva {
        let mut trees = IdVec::new();
        let mut tree_paths = HashMap::new();

        for (path, res) in results {
            let tree = SylvaTree {
                tree: res.tree,
                reports: res.reports,
                path: path.clone(),
            };

            let tree_id = trees.insert(tree).into();

            tree_paths.insert(path, tree_id);
        }

        Sylva { trees, tree_paths }
    }

    pub fn iter(&self) -> impl Iterator<Item = (SylvaTreeId, &SylvaTree)> {
        self.trees.iter().map(|(id, t)| (id.into(), t))
    }

    pub fn reports(&self) -> impl Iterator<Item = (&Source, &[Report])> {
        self.trees.iter().filter_map(|(_, t)| {
            if !t.reports.is_empty() {
                Some((&t.tree.source, t.reports.as_slice()))
            } else {
                None
            }
        })
    }

    pub fn tree(&self, id: SylvaTreeId) -> Option<&SourceTree> {
        self.trees.get(id.0).map(|t| &t.tree)
    }

    pub fn tree_from_path(&self, path: impl AsRef<Path>) -> Option<&SourceTree> {
        self.tree_paths
            .get(path.as_ref())
            .and_then(|id| self.trees.get(id.0))
            .map(|tree| &tree.tree)
    }

    pub fn build_concurrently(
        parser: SylvaParser,
        sources: impl IntoParallelIterator<Item = Source>,
    ) -> anyhow::Result<Sylva> {
        let parsing_results = sources
            .into_par_iter()
            .map(|s| {
                let path = s.path().into();
                let res = parser.clone().run(s);
                (path, res)
            })
            .collect();

        Ok(Sylva::new(parsing_results))
    }

    pub fn build(
        spec: &Spec,
        start_rule: &str,
        sources: impl Iterator<Item = Source>,
    ) -> anyhow::Result<Sylva> {
        let init_parser_runner = ParserRunner::new(start_rule, &spec.syntax)?;

        let parsing_results = sources
            .map(|s| parse_source(&init_parser_runner, s))
            .collect();

        Ok(Sylva::new(parsing_results))
    }
}

fn parse_source(runner: &ParserRunner, source: Source) -> (PathBuf, ParsingResult) {
    let path = source.path().into();
    let res = runner.run_once(source);
    (path, res)
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use maplit::{hashmap, hashset};
    use once_cell::sync::Lazy;

    use crate::{
        core::{
            pos::{InclPosRange, Pos},
            source::test::create_test_source_tree,
        },
        report::ReportKind,
    };

    use super::*;

    static TEST_TREE_1: Lazy<SourceTree> = Lazy::new(|| create_test_source_tree("some code"));

    static TEST_TREE_2: Lazy<SourceTree> = Lazy::new(|| create_test_source_tree("some more code"));
    static TEST_TREE_2_REPORT: Lazy<Report> = Lazy::new(|| Report {
        file_path: "file2".into(),
        code: "Some random error".to_string(),
        kind: ReportKind::Error,
        position: InclPosRange::new(Pos::new((1, 1), 0), Pos::new((1, 1), 0)).unwrap(),
        message: "".to_string(),
        note: None,
    });

    static TEST_SYLVA: Lazy<Sylva> = Lazy::new(|| {
        Sylva::new(hashmap! {
            "file1".into() => ParsingResult { tree: TEST_TREE_1.clone(), reports: vec![] },
            "file2".into() => ParsingResult {
                tree: TEST_TREE_2.clone(),
                reports: vec![
                    TEST_TREE_2_REPORT.clone()
                ]
            }
        })
    });

    #[test]
    fn create_sylva() {
        let sylva = TEST_SYLVA.clone();

        assert_eq!(sylva.tree_from_path("file1"), Some(&TEST_TREE_1.clone()));
        assert_eq!(sylva.tree_from_path("file2"), Some(&TEST_TREE_2.clone()));

        assert_eq!(
            &sylva.trees.into_iter().collect::<HashSet<_>>(),
            &hashset!(
                SylvaTree {
                    tree: TEST_TREE_1.clone(),
                    path: "file1".into(),
                    reports: vec![]
                },
                SylvaTree {
                    tree: TEST_TREE_2.clone(),
                    path: "file2".into(),
                    reports: vec![TEST_TREE_2_REPORT.clone()]
                }
            )
        );
    }

    #[test]
    fn sylva_iter() {
        let sylva = TEST_SYLVA.clone();

        for (id, tree) in sylva.iter() {
            assert_eq!(sylva.tree_paths.get(&tree.path), Some(&id));
        }
    }

    #[test]
    fn sylva_reports() {
        let sylva = TEST_SYLVA.clone();

        assert_eq!(
            sylva.reports().collect::<Vec<_>>(),
            vec![(
                &Source::inline(
                    "some more code".to_string(),
                    "some more code_id".to_string(),
                ),
                [TEST_TREE_2_REPORT.clone()].as_slice()
            )]
        )
    }

    #[test]
    fn tree_ok() {
        let sylva = TEST_SYLVA.clone();

        let file1_id = sylva.tree_paths.get(Path::new("file1")).unwrap();

        assert_eq!(sylva.tree(*file1_id).unwrap(), &TEST_TREE_1.clone())
    }

    #[test]
    fn tree_notok() {
        let sylva = TEST_SYLVA.clone();

        let non_existing_id = 999.into();

        assert_eq!(sylva.tree(non_existing_id), None);
    }

    #[test]
    fn tree_from_path() {
        let sylva = TEST_SYLVA.clone();
        assert_eq!(
            sylva.tree_from_path(Path::new("file1")).unwrap(),
            &TEST_TREE_1.clone()
        );
    }

    #[allow(dead_code)]
    fn create_test_sylva(prefix: Option<&str>) -> Sylva {
        let prefix = prefix.unwrap_or_default();
        let test_tree1 = create_test_source_tree(&format!("{prefix} some code"));
        let test_tree2 = create_test_source_tree(&format!("{prefix} some more code"));
        let test_tree2_report = Report {
            file_path: "file2".into(),
            code: "Some random error".to_string(),
            kind: ReportKind::Error,
            position: InclPosRange::new(Pos::new((1, 1), 0), Pos::new((1, 1), 0)).unwrap(),
            message: "".to_string(),
            note: None,
        };

        Sylva::new(hashmap! {
            "file1".into() => ParsingResult { tree: test_tree1.clone(), reports: vec![] },
            "file2".into() => ParsingResult {
                tree: test_tree2.clone(),
                reports: vec![
                    test_tree2_report
                ]
            }
        })
    }
}
