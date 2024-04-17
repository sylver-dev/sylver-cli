use std::any::TypeId;

use anyhow::Context;
use itertools::Itertools;
use rustyline::{
    error::ReadlineError,
    validate::{ValidationContext, ValidationResult, Validator},
    Editor,
};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};

use sylver_core::{
    land::{cmds::filter_sylva, sylva::SylvaId, Land},
    pretty_print::tree::{render_node, TreePPrint},
    query::{
        expr::{
            EvalCtx, EvalError, EvalIterator, Expr, Extension, ExtensionExpr, SpecialIdentifier,
            Value,
        },
        language::compile::{compile, compile_expr},
        RawTreeInfoBuilder, SylvaNode, TreeInfoBuilder,
    },
    script::python::PythonScriptEngine,
    tree::info::{raw::RawTreeInfo, TreeInfo},
};

use sylver_dsl::sylq::{parse_expr, parse_query};

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
        run_term(ctx, stripped);
    }

    println!()
}

fn run_term(ctx: &mut ReplCtx, line: &str) {
    println!();

    let result = if line.starts_with("match") {
        run_query(ctx, line)
    } else {
        eval_and_print(ctx, line)
    };

    if let Err(e) = result {
        eprintln!("{e:?}")
    }
}

fn run_query(ctx: &mut ReplCtx, query_code: &str) -> anyhow::Result<()> {
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

fn eval_and_print(ctx: &mut ReplCtx, expr_code: &str) -> anyhow::Result<()> {
    let value = eval_expr(ctx, expr_code).context("failed to evaluate expression")?;
    print_value(ctx, &value);
    Ok(())
}

fn eval_expr(ctx: &ReplCtx, expr_code: &str) -> anyhow::Result<Value<'static>> {
    let parsed_expr = parse_expr(expr_code).context("Failed to parse query")?;
    let compiled_expr: Expr = compile_expr(ctx.land.sylva_spec(ctx.sylva), &parsed_expr)
        .context("Failed to compile query")?;

    let mut eval_ctx = build_eval_ctx(ctx);
    let extension = GenCacheSpecialIdentifierExtension {
        cache: &ctx.nodes_cache,
    };
    eval_ctx.add_extension(TypeId::of::<SpecialIdentifier>(), &extension);

    compiled_expr
        .eval(&mut eval_ctx)
        .map(|v| v.to_static())
        .context("failed to evaluate expression")
}

fn build_eval_ctx<'a>(ctx: &'a ReplCtx<'a>) -> EvalCtx<'_, RawTreeInfoBuilder<'_>> {
    let spec = ctx.land.sylva_spec(ctx.sylva);

    EvalCtx::new(
        spec,
        RawTreeInfoBuilder::new(spec, ctx.land.sylva(ctx.sylva)),
        ctx.land,
        PythonScriptEngine::default(),
    )
}

fn print_value(ctx: &ReplCtx, value: &Value) {
    println!("{}", format_value(ctx, value));
}

fn format_value(ctx: &ReplCtx, value: &Value) -> String {
    match value {
        Value::Null => "null".to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Int(i) => i.to_string(),
        Value::String(s) => s.to_string(),
        Value::List(l) => format_list(ctx, l),
        Value::Generator(g) => {
            let mut values_iter = g.iter();
            let eval_ctx = build_eval_ctx(ctx);

            let mut values = Vec::new();
            while let Some(v) = values_iter.next_value(&eval_ctx) {
                values.push(v);
            }

            format_list(ctx, &values)
        }
        Value::Kind(k) => ctx
            .land
            .sylva_spec(ctx.sylva)
            .syntax
            .kind_name(*k)
            .to_string(),
        Value::Node(n) => render_node(
            ctx.land.sylva_spec(ctx.sylva),
            ctx.land.sylva_node_tree(*n),
            n.node,
        ),
    }
}

fn format_list<'v>(ctx: &ReplCtx, list: impl IntoIterator<Item = &'v Value<'v>>) -> String {
    let formatted_values = list.into_iter().map(|v| format_value(ctx, v)).join(", ");
    format!("[{formatted_values}]")
}

#[derive(Debug, Clone)]
enum Cmd {
    Quit,
    Print(PrintableTerm),
    PrintAst(PrintableTerm),
}

#[derive(Debug, Clone)]
enum PrintableTerm {
    Expr(String),
    Path(String),
}

fn parse_command(line: &str) -> Option<Cmd> {
    let components: Vec<&str> = line.split(' ').collect();

    let cmd = match components.as_slice() {
        ["quit"] => Cmd::Quit,
        ["print", path] => Cmd::Print(parse_printable_term(path.to_string())?),
        ["print_ast", path] => Cmd::PrintAst(parse_printable_term(path.to_string())?),
        _ => return None,
    };

    Some(cmd)
}

fn parse_printable_term(term: String) -> Option<PrintableTerm> {
    if term.starts_with('$') {
        Some(PrintableTerm::Expr(term))
    } else {
        Some(PrintableTerm::Path(term))
    }
}

fn run_command(ctx: &ReplCtx, line: &str) {
    let cmd = parse_command(line).expect("Invalid command");

    match cmd {
        Cmd::Quit => std::process::exit(0),
        Cmd::Print(term) => print_src(ctx, &term),
        Cmd::PrintAst(path) => print_ast(ctx, &path),
    }
}

fn print_src(ctx: &ReplCtx, id: &PrintableTerm) {
    println!();

    let sylva = ctx.land.sylva(ctx.sylva);

    match id {
        PrintableTerm::Path(path) => {
            if let Some(tree) = sylva.tree_from_path(path) {
                println!("{}", tree.source.src());
            } else {
                println!("No such file: {path}");
            }
        }
        PrintableTerm::Expr(expr) => {
            let value = eval_expr(ctx, expr).expect("failed to evaluate expression");

            if let Value::Node(n) = value {
                let tree = ctx.land.sylva_node_tree(n);
                let spec = ctx.land.sylva_spec(n.sylva);
                let info = RawTreeInfo::new(tree, &spec.syntax);
                println!("{}", info.node_text(n.node));
            } else {
                println!("Not a node: {}", format_value(ctx, &value));
            }
        }
    }
}

fn print_ast(ctx: &ReplCtx, id: &PrintableTerm) {
    println!();

    let sylva = ctx.land.sylva(ctx.sylva);
    let spec = ctx.land.sylva_spec(ctx.sylva);

    match id {
        PrintableTerm::Path(path) => {
            if let Some(tree) = sylva.tree_from_path(path) {
                let repr = TreePPrint::new(RawTreeInfo::new(tree, &spec.syntax)).render();
                println!("{repr}");
            } else {
                println!("No such file: {path}");
            }
        }
        PrintableTerm::Expr(expr) => {
            let value = eval_expr(ctx, expr).expect("failed to evaluate expression");

            if let Value::Node(n) = value {
                let tree = ctx.land.sylva_node_tree(n);
                let info = RawTreeInfo::new(tree, &spec.syntax);
                let repr = TreePPrint::new(info).render_from(0, None, &info.proxy(n.node));
                println!("{repr}");
            } else {
                println!("Not a node: {}", format_value(ctx, &value));
            }
        }
    }
}

struct GenCacheSpecialIdentifierExtension<'cache> {
    cache: &'cache cache::GenCache<SylvaNode>,
}

impl<'v, 'cache: 'v, B: TreeInfoBuilder<'v>> Extension<'v, B>
    for GenCacheSpecialIdentifierExtension<'cache>
{
    fn eval(
        &self,
        _ctx: &mut EvalCtx<'v, B>,
        expr: &ExtensionExpr,
    ) -> Result<Value<'v>, EvalError> {
        match expr {
            ExtensionExpr::SpecialIdentifier(s) => {
                let identifier = s.identifier();
                let node_index = identifier
                    .parse::<usize>()
                    .map_err(|_| EvalError::InvalidIdentifier(identifier.to_string()))?;

                self.cache
                    .get(node_index)
                    .ok_or_else(|| EvalError::InvalidIdentifier(identifier.to_string()))
                    .map(|node| Value::Node(*node))
            }
        }
    }
}
