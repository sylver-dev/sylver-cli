use anyhow::Context;
use rustyline::{
    error::ReadlineError,
    validate::{ValidationContext, ValidationResult, Validator},
    Editor,
};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};

use sylver_core::{
    land::{cmds::filter_sylva, sylva::SylvaId, Land},
    pretty_print::tree::{render_node, TreePPrint},
    query::{language::compile::compile, SylvaNode},
    script::python::PythonScriptEngine,
    tree::info::{raw::RawTreeInfo, TreeInfo},
};

use sylver_dsl::sylq::parse_query;

mod cache;

#[derive(Copy, Clone, Default, Completer, Helper, Highlighter, Hinter)]
struct CommandsValidator {}

impl Validator for CommandsValidator {
    fn validate(&self, ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        let result = if ctx.input().starts_with(':') {
            let stripped = strip_punctuation(ctx.input());
            if parse_command(stripped).is_some() {
                ValidationResult::Valid(None)
            } else {
                ValidationResult::Invalid(Some(format!("\nInvalid command: {stripped}")))
            }
        } else if ctx.input().ends_with(';') {
            ValidationResult::Valid(None)
        } else {
            ValidationResult::Incomplete
        };

        Ok(result)
    }
}

#[derive(Debug, Clone)]
struct ReplCtx<'l> {
    land: &'l Land,
    sylva: SylvaId,
    nodes_cache: cache::GenCache<SylvaNode>,
}

pub fn start_repl(land: &Land, sylva: SylvaId) -> anyhow::Result<()> {
    let mut rl = Editor::new().context("Could not build prompt")?;
    rl.set_helper(Some(CommandsValidator::default()));

    let mut ctx = ReplCtx {
        land,
        sylva,
        nodes_cache: Default::default(),
    };

    loop {
        match rl.readline("λ> ") {
            Ok(line) => {
                rl.add_history_entry(&line);
                process_input(&mut ctx, &line);
            }
            Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                break;
            }
            err => {
                err.context("Readline error")?;
            }
        }
    }

    Ok(())
}

fn strip_punctuation(line: &str) -> &str {
    line.strip_prefix(':')
        .or_else(|| line.strip_suffix(';'))
        .unwrap_or(line)
}

fn process_input(ctx: &mut ReplCtx, line: &str) {
    let stripped = strip_punctuation(line);

    if line.starts_with(':') {
        run_command(ctx, stripped);
    } else {
        run_query(ctx, stripped);
    }

    println!()
}

fn run_query(ctx: &mut ReplCtx, line: &str) {
    println!();
    if let Err(e) = do_run_query(ctx, line) {
        eprintln!("{e:?}")
    }
}

fn do_run_query(ctx: &mut ReplCtx, query_code: &str) -> anyhow::Result<()> {
    let spec = ctx.land.sylva_spec(ctx.sylva);

    let query = parse_query(query_code).context("Failed to parse query")?;
    let query_predicate = compile(spec, &query).context("Failed to compile query")?;

    ctx.nodes_cache.start_generation();

    for sylva_node in filter_sylva(
        ctx.land,
        PythonScriptEngine::default(),
        ctx.sylva,
        &query_predicate,
    )? {
        let cache_id = ctx.nodes_cache.push(sylva_node);
        let tree = ctx.land.sylva_node_tree(sylva_node);
        println!("${cache_id} {}", render_node(spec, tree, sylva_node.node))
    }

    Ok(())
}

#[derive(Debug, Clone)]
enum Cmd {
    Quit,
    Print(PrintableId),
    PrintAst(PrintableId),
}

#[derive(Debug, Clone)]
enum PrintableId {
    CacheId(usize),
    Path(String),
}

fn parse_command(line: &str) -> Option<Cmd> {
    let components: Vec<&str> = line.split(' ').collect();

    let cmd = match components.as_slice() {
        ["quit"] => Cmd::Quit,
        ["print", path] => Cmd::Print(parse_printable_id(path.to_string())?),
        ["print_ast", path] => Cmd::PrintAst(parse_printable_id(path.to_string())?),
        _ => return None,
    };

    Some(cmd)
}

fn parse_printable_id(id: String) -> Option<PrintableId> {
    if let Some(stripped) = id.strip_prefix('$') {
        let index = stripped.parse().ok()?;
        Some(PrintableId::CacheId(index))
    } else {
        Some(PrintableId::Path(id))
    }
}

fn run_command(ctx: &ReplCtx, line: &str) {
    let cmd = parse_command(line).expect("Invalid command");

    match cmd {
        Cmd::Quit => std::process::exit(0),
        Cmd::Print(path) => print_src(ctx, &path),
        Cmd::PrintAst(path) => print_ast(ctx, &path),
    }
}

fn print_src(ctx: &ReplCtx, id: &PrintableId) {
    println!();

    let sylva = ctx.land.sylva(ctx.sylva);

    match id {
        PrintableId::Path(path) => {
            if let Some(tree) = sylva.tree_from_path(path) {
                println!("{}", tree.source.src());
            } else {
                println!("No such file: {path}");
            }
        }
        PrintableId::CacheId(id) => {
            let node = ctx.nodes_cache.get(*id);

            match node {
                Some(n) => {
                    let tree = ctx.land.sylva_node_tree(*n);
                    let spec = ctx.land.sylva_spec(n.sylva);
                    let info = RawTreeInfo::new(tree, &spec.syntax);
                    println!("{}", info.node_text(n.node));
                }
                None => println!("Missing entry: ${id}"),
            }
        }
    }
}

fn print_ast(ctx: &ReplCtx, id: &PrintableId) {
    println!();

    let sylva = ctx.land.sylva(ctx.sylva);
    let spec = ctx.land.sylva_spec(ctx.sylva);

    match id {
        PrintableId::Path(path) => {
            if let Some(tree) = sylva.tree_from_path(path) {
                let repr = TreePPrint::new(RawTreeInfo::new(tree, &spec.syntax)).render();
                println!("{repr}");
            } else {
                println!("No such file: {path}");
            }
        }
        PrintableId::CacheId(id) => match ctx.nodes_cache.get(*id) {
            Some(n) => {
                let tree = ctx.land.sylva_node_tree(*n);
                let spec = ctx.land.sylva_spec(n.sylva);
                let info = RawTreeInfo::new(tree, &spec.syntax);
                let repr = TreePPrint::new(info).render_from(0, None, &info.proxy(n.node));
                println!("{repr}");
            }
            None => println!("Missing entry: ${id}"),
        },
    }
}
