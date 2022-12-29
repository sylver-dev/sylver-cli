use itertools::Itertools;

use crate::{
    core::{
        source::{Source, SourceTree},
        spec::Syntax,
    },
    parsing::{build_table, scanner::Scanner, sppf_to_tree, Parser, ParsingTable},
    report::Report,
    tree::Tree,
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ParsingResult {
    pub tree: SourceTree,
    pub reports: Vec<Report>,
}

#[derive(Debug, Clone)]
pub struct ParserRunner<'s> {
    table: ParsingTable,
    scanner: Scanner,
    syntax: &'s Syntax,
}

impl<'s> ParserRunner<'s> {
    pub fn new(start_rule: &str, syntax: &'s Syntax) -> anyhow::Result<Self> {
        let table = build_table(syntax, start_rule)?;
        let scanner = Scanner::new(
            syntax
                .terminals()
                .map(|(tag, term)| (tag, term.reg.clone())),
        )?;
        Ok(ParserRunner {
            table,
            scanner,
            syntax,
        })
    }

    pub fn run(&self, sources: impl IntoIterator<Item = Source>) -> Vec<ParsingResult> {
        sources.into_iter().map(|s| self.run_once(s)).collect()
    }

    pub fn run_once(&self, source: Source) -> ParsingResult {
        let mut parser = Parser::new(self.syntax, &self.table, &self.scanner, source.src());
        parser.parse();

        let (tree, tokens) =
            sppf_to_tree(self.syntax, &parser.tree).unwrap_or_else(|_| (Tree::new(), vec![]));

        let reports = parser
            .collect_errors()
            .iter()
            .flat_map(|e| e.to_reports(&parser, source.path()))
            .unique()
            .collect();

        ParsingResult {
            tree: SourceTree::new(source, tokens, tree),
            reports,
        }
    }
}

#[cfg(test)]
mod tests {
    use sylver_dsl::meta::parse;

    use crate::core::spec::Spec;

    use super::*;

    #[test]
    fn run_parser_ok() {
        let spec = test_spec_and_grammar();
        let parser_runner =
            ParserRunner::new("main", &spec.syntax).expect("Cannot create parser runner");

        let source = Source::inline("1+1".into(), "buffer".into());

        let result = parser_runner.run([source]);

        match result.as_slice() {
            [r] if r.reports.is_empty() => (),
            _ => panic!("Expected a result with 1 tree and 0 reports but got {result:?}"),
        }
    }

    fn test_spec_and_grammar() -> Spec {
        let declarations =
            parse(include_str!("../../test_res/specs/binop.syl")).expect("Invalid spec");

        let spec = Spec::from_decls(declarations).expect("Invalid spec");

        spec
    }
}
