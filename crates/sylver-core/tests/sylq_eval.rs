use std::path::PathBuf;

use itertools::Itertools;
use test_generator::test_resources;

use sylver_core::{
    core::{
        source::{source_from_file, Source},
        spec::{Spec, DEFAULT_START_RULE},
    },
    land::{
        builder::LandBuilder,
        cmds::filter_sylva,
        sylva::{Sylva, SylvaId, SylvaParser},
        Land, LandSpecId,
    },
    parsing::parser_runner::ParserRunner,
    pretty_print::tree::render_node,
    query::{expr::EvalError, language::compile::compile, SylvaNode},
};
use sylver_dsl::sylq::parse_query;

#[test_resources("crates/sylver-core/test_res/sylq_eval/**/*.sylq")]
fn test_sylq_eval(expr_input: &str) {
    let expr_relative = PathBuf::from(get_relative_path(expr_input));
    let dir = expr_relative.parent().unwrap().to_owned();
    let spec_file = glob_existing(&format!("{}/*.syl", dir.display()));

    let spec = Spec::from_decls(
        sylver_dsl::meta::parse(&std::fs::read_to_string(spec_file).unwrap()).unwrap(),
    )
    .unwrap();

    let sources: Vec<Source> = glob(&format!("{}/src/*", dir.display()))
        .map(|p| source_from_file(&p).unwrap())
        .collect();

    let mut land_builder = LandBuilder::new();
    let spec_id = land_builder.add_spec(spec.clone());
    let parser = ParserRunner::new(DEFAULT_START_RULE, &spec.syntax).unwrap();
    let sylva = Sylva::build_concurrently(SylvaParser::Custom(parser), sources).unwrap();
    let sylva_id = land_builder
        .add_sylva(sylva, LandSpecId::CustomLangId(spec_id))
        .unwrap();

    let land = land_builder.build();

    let expr = parse_query(std::fs::read_to_string(&expr_relative).unwrap()).unwrap();

    let compiled = compile(land.spec(LandSpecId::CustomLangId(spec_id)), &expr).unwrap();

    let res = filter_sylva(&land, sylva_id, &compiled);

    let expected_output = std::fs::read_to_string(expr_relative.with_extension("output")).unwrap();
    let output_str = res_to_string(&land, sylva_id, res);

    assert_eq!(output_str, expected_output);
}

fn res_to_string(land: &Land, sylva: SylvaId, res: Result<Vec<SylvaNode>, EvalError>) -> String {
    match res {
        Err(e) => format!("{e}"),
        Ok(vals) => vals
            .iter()
            .map(|v| val_to_string(land, sylva, v))
            .join("\n"),
    }
}

fn val_to_string(land: &Land, sylva: SylvaId, val: &SylvaNode) -> String {
    let tree = land.sylva_node_tree(*val);
    render_node(land.sylva_spec(sylva), tree, val.node)
}

fn glob_existing(pattern: &str) -> PathBuf {
    glob::glob(pattern).unwrap().next().unwrap().unwrap()
}

fn glob(pattern: &str) -> impl Iterator<Item = PathBuf> {
    glob::glob(pattern).unwrap().map(|r| r.unwrap())
}

fn get_relative_path(output_path: &str) -> String {
    fancy_regex::Regex::new(".*/sylver-core/")
        .unwrap()
        .replace(output_path, "")
        .to_string()
}
