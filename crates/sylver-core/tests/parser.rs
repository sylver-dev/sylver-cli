use std::{
    fs::read_to_string,
    path::{Path, PathBuf},
};

use thiserror::__private::PathAsDisplay;

use sylver_core::{
    core::{source::Source, spec::spec_from_file},
    parsing::parser_runner::ParserRunner,
    pretty_print::{render_report, tree::TreePPrint},
    tree::info::raw::RawTreeInfo,
};

#[derive(Debug, Clone)]
struct ParserTestCase {
    input: PathBuf,
    expected: PathBuf,
}

#[derive(Debug, Clone)]
struct ParserTestSpec {
    spec: PathBuf,
    cases: Vec<ParserTestCase>,
}

#[test]
fn parser_single_positives() {
    let specs = fetch_single_positive_specs();

    for spec in specs {
        eval_parser_test_spec(spec);
    }
}

fn fetch_single_positive_specs() -> Vec<ParserTestSpec> {
    glob::glob("test_res/**/*.syl")
        .expect("Failed to spec glob pattern")
        .map(|s| read_test_spec(s.unwrap()))
        .collect()
}

fn read_test_spec(spec_file: PathBuf) -> ParserTestSpec {
    let cases = spec_output_files(&spec_file)
        .map(test_case_from_output)
        .collect();

    ParserTestSpec {
        spec: spec_file,
        cases,
    }
}

fn spec_output_files(spec_file: &Path) -> impl Iterator<Item = PathBuf> {
    let spec_dir = spec_file.parent().unwrap();

    glob::glob(&format!(
        "{}/parser_tests/single_positive/*.output",
        spec_dir.as_display()
    ))
    .expect("Failed to read output glob")
    .map(|r| r.unwrap())
}

fn test_case_from_output(output_path: PathBuf) -> ParserTestCase {
    let input_glob = fancy_regex::Regex::new("output$")
        .unwrap()
        .replace(output_path.to_str().unwrap(), "*")
        .to_string();

    let input = glob::glob(&input_glob).unwrap().next().unwrap().unwrap();

    ParserTestCase {
        input,
        expected: output_path,
    }
}

fn eval_parser_test_spec(test_spec: ParserTestSpec) {
    let spec = spec_from_file(&test_spec.spec).unwrap();
    let parser_runner =
        ParserRunner::new("main", &spec.syntax).expect("Failed to build parser runner");

    for case in test_spec.cases {
        println!("{}", case.input.to_string_lossy());

        let input_code = read_to_string(&case.input).expect("Failed to read input file");
        let parse_res = parser_runner
            .run([Source::inline(input_code, "buffer".into())])
            .pop()
            .unwrap();

        if !parse_res.reports.is_empty() {
            for r in &parse_res.reports {
                println!(
                    "{}",
                    render_report(true, r, &parse_res.tree.source).unwrap()
                );
            }
            panic!("Parsing error");
        }

        let expected = read_to_string(&case.expected).expect("Failed to read expected output");
        let rendered_tree =
            TreePPrint::new(RawTreeInfo::new(&parse_res.tree, &spec.syntax)).render();

        if rendered_tree != expected {
            assert_eq!(rendered_tree, expected.strip_suffix('\n').unwrap())
        }
    }
}
