use sylver_core::{
    builtin_langs::{get_builtin_lang, parser::BuiltinParserRunner},
    core::{
        source::Source,
        spec::{Spec, DEFAULT_START_RULE},
    },
    land::{
        builder::LandBuilder,
        cmds::{exec_rules, parsing_errors, RuleResult},
        sylva::{Sylva, SylvaId, SylvaParser},
        Land, LandSpecId,
    },
    parsing::parser_runner::ParserRunner,
    pretty_print::render_report,
    specs::{loader::SylverLoader, stem::project::ProjectLang},
};

pub fn verify_land(color: bool, land: &Land) -> anyhow::Result<()> {
    print_land_reports(color, land)?;
    let res = run_land_rules(color, land)?;

    if !res.is_empty() {
        std::process::exit(1);
    }

    Ok(())
}

pub fn print_land_reports(color: bool, land: &Land) -> anyhow::Result<()> {
    for (source, reports) in parsing_errors(land) {
        for report in reports {
            let report_repr = render_report(color, report, source)?;
            println!("{report_repr}")
        }
    }

    Ok(())
}

pub fn run_land_rules(color: bool, land: &Land) -> anyhow::Result<Vec<RuleResult>> {
    let mut exec_res = exec_rules(land)?;

    exec_res.sort_by_key(|r| {
        let category = r.rule(land).category;
        (category, r.ruleset, r.node)
    });

    exec_res.reverse();

    for res in &exec_res {
        let report = res.to_report(land);
        let source = res.source(land);
        let report_repr = render_report(color, &report, source)?;
        println!("{report_repr}")
    }

    Ok(exec_res)
}

pub fn build_sylva(
    loader: &SylverLoader,
    builder: &mut LandBuilder,
    language: &ProjectLang,
    sources: Vec<Source>,
) -> anyhow::Result<SylvaId> {
    match language {
        ProjectLang::Custom(location) => {
            let spec = loader.load_language_spec(location)?;
            let parser = ParserRunner::new(DEFAULT_START_RULE, &spec.syntax)?;
            let sylva = Sylva::build_concurrently(SylvaParser::Custom(parser), sources)?;
            let spec_id = LandSpecId::CustomLangId(builder.add_spec(spec));
            builder.add_sylva(sylva, spec_id)
        }
        ProjectLang::Builtin(b) => {
            let (mappings, lang) = get_builtin_lang(*b);
            let syntax = mappings.types.as_slice().into();
            let parser = BuiltinParserRunner::new(lang, &syntax, mappings);
            let sylva = Sylva::build_concurrently(SylvaParser::Builtin(parser), sources)?;
            let spec = Spec::from_syntax(syntax);
            let spec_id = LandSpecId::BuiltinLangId(builder.add_spec(spec));
            builder.add_sylva(sylva, spec_id)
        }
    }
}
