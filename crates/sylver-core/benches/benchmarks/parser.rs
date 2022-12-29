use std::{
    path::{Path, PathBuf},
    time::Duration,
};

use criterion::{black_box, criterion_group, Criterion};

use sylver_core::{
    core::{source::source_from_file, spec::spec_from_file},
    parsing::parser_runner::ParserRunner,
};

fn parser_benchmark(c: &mut Criterion) {
    c.bench_function("parser", |b| b.iter(|| bench_all_specs(black_box(()))));
}

fn bench_all_specs(_: ()) {
    glob::glob("test_res/**/*.syl")
        .unwrap()
        .for_each(|spec| benches_for_spec(&spec.unwrap()));
}

fn benches_for_spec(spec_file: &Path) {
    let bench_files: Vec<PathBuf> = glob::glob(&format!(
        "{}/benches/*",
        spec_file.as_os_str().to_string_lossy()
    ))
    .unwrap()
    .collect::<Result<_, _>>()
    .unwrap();

    let spec = spec_from_file(spec_file).unwrap();
    let parser_runner = ParserRunner::new("main", &spec.syntax).unwrap();

    parser_runner.run(bench_files.iter().map(|p| source_from_file(p).unwrap()));
}

criterion_group!(
    name = parser;
    config = Criterion::default().measurement_time(Duration::from_secs(8));
    targets = parser_benchmark
);
