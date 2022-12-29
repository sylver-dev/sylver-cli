use std::{error::Error, fmt::Debug};

use pest::{iterators::Pairs, Parser, RuleType};

use crate::{
    meta::{term_content, MetaParser, Rule, TermContent},
    util::{WalkError, Walkable},
};

pub fn parse_term_content(reg_str: impl AsRef<str>) -> TermContent {
    match MetaParser::parse(Rule::term_content, reg_str.as_ref()) {
        Ok(mut tree) => term_content(tree.next_child().unwrap().into_inner()).unwrap(),
        Err(e) => panic!("{e}"),
    }
}

pub fn test_parser<'a, T, E, F, R>(
    input: Result<Pairs<'a, R>, pest::error::Error<R>>,
    parse_fn: F,
    expected: T,
) where
    T: PartialEq + Debug,
    E: Error + From<pest::error::Error<R>> + From<WalkError<R>>,
    F: Fn(Pairs<'a, R>) -> Result<T, E>,
    R: RuleType,
{
    let node = build_node(input, parse_fn);
    assert_eq!(node, expected);
}

fn build_node<'a, R, E, F, T>(input: Result<Pairs<'a, R>, pest::error::Error<R>>, parse_fn: F) -> T
where
    E: Error + From<pest::error::Error<R>> + From<WalkError<R>>,
    F: Fn(Pairs<'a, R>) -> Result<T, E>,
    R: RuleType,
{
    let parse_tree = input
        .map_err(Into::into)
        .and_then(|mut p| parse_fn(p.next_child()?.into_inner()));

    match parse_tree {
        Ok(tree) => tree,
        Err(e) => panic!("{}", e),
    }
}
