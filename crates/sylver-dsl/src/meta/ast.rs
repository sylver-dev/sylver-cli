use std::{
    collections::{BTreeMap, HashMap},
    fs::read_to_string,
    hash::{Hash, Hasher},
    io,
    path::Path,
};

use itertools::Itertools;
use non_empty_vec::NonEmpty;
use pest::{
    self,
    iterators::{Pair, Pairs},
    Parser,
};
use pest_derive::*;
use thiserror::Error;

use crate::util::*;

type MetaParserRes<T> = Result<T, MetaParserErr>;

#[derive(Debug, Error)]
pub enum MetaParserErr {
    #[error(transparent)]
    PestErr(Box<pest::error::Error<Rule>>),
    #[error(transparent)]
    Walk(#[from] WalkError<Rule>),
    #[error(transparent)]
    IO(#[from] io::Error),
    #[error(transparent)]
    RegexParsing(#[from] fancy_regex::Error),
    #[error("Unknown term type: {0}")]
    UnknownTermType(String),
    #[error("Missing argument: {0}")]
    MissingArgument(String),
}

impl From<pest::error::Error<Rule>> for MetaParserErr {
    fn from(e: pest::error::Error<Rule>) -> Self {
        MetaParserErr::PestErr(Box::new(e))
    }
}

#[derive(Parser)]
#[grammar = "meta/meta.pest"]
pub struct MetaParser {}

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Decl {
    Node(NodeDecl),
    Terminal(TermDecl),
    Rule(RuleDecl),
}

impl Decl {
    pub fn name(&self) -> &str {
        match self {
            Decl::Node(n) => &n.name,
            Decl::Terminal(t) => &t.name,
            Decl::Rule(r) => &r.name,
        }
    }

    pub fn is_node(&self) -> bool {
        matches!(self, Decl::Node(_))
    }

    pub fn is_term(&self) -> bool {
        matches!(self, Decl::Terminal(_))
    }

    pub fn is_rule(&self) -> bool {
        matches!(self, Decl::Rule(_))
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct NodeDecl {
    pub name: String,
    pub parent_type: Option<String>,
    pub fields: BTreeMap<String, TypeLit>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum TypeLit {
    Simple(SimpleTypeLit),
    Or(OrTypeLit),
}

impl TypeLit {
    pub const LIST_TYPE: &'static str = "List";

    pub fn from_simple_types(types: impl IntoIterator<Item = SimpleTypeLit>) -> Option<TypeLit> {
        let mut types_iter = types.into_iter().peekable();

        let first = types_iter.next()?;

        if types_iter.peek().is_none() {
            Some(TypeLit::Simple(first))
        } else {
            let rest = types_iter.collect();
            Some(TypeLit::Or(OrTypeLit {
                alts: NonEmpty::from((first, rest)),
            }))
        }
    }

    pub fn list_of(elem_type: TypeLit) -> TypeLit {
        TypeLit::Simple(SimpleTypeLit {
            name: TypeLit::LIST_TYPE.into(),
            parameters: vec![elem_type],
        })
    }

    pub fn from_name(name: String) -> TypeLit {
        TypeLit::Simple(SimpleTypeLit {
            name,
            parameters: vec![],
        })
    }

    pub fn parameters(&self) -> &[TypeLit] {
        match self {
            TypeLit::Simple(SimpleTypeLit { parameters, .. }) => parameters,
            _ => &[],
        }
    }

    pub fn is_list(&self) -> bool {
        matches!(self, TypeLit::Simple(SimpleTypeLit { name, ..}) if name == TypeLit::LIST_TYPE)
    }
}

impl ToString for TypeLit {
    fn to_string(&self) -> String {
        match self {
            TypeLit::Simple(s) => s.to_string(),
            TypeLit::Or(o) => o.to_string(),
        }
    }
}

pub fn list_elems_type(t: &TypeLit) -> Option<&TypeLit> {
    if t.is_list() && t.parameters().len() == 1 {
        Some(&t.parameters()[0])
    } else {
        None
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct SimpleTypeLit {
    pub name: String,
    pub parameters: Vec<TypeLit>,
}

impl SimpleTypeLit {
    pub fn new(name: String, parameters: Vec<TypeLit>) -> SimpleTypeLit {
        SimpleTypeLit { name, parameters }
    }
    pub fn from_name(name: String) -> SimpleTypeLit {
        Self::new(name, vec![])
    }
}

impl ToString for SimpleTypeLit {
    fn to_string(&self) -> String {
        let params_str = if self.parameters.is_empty() {
            String::new()
        } else {
            format!(
                "<{}>",
                self.parameters.iter().map(|p| p.to_string()).join(", ")
            )
        };

        format!("{}{}", self.name, params_str)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct OrTypeLit {
    pub alts: NonEmpty<SimpleTypeLit>,
}

impl ToString for OrTypeLit {
    fn to_string(&self) -> String {
        self.alts.iter().map(|a| a.to_string()).join(" | ")
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct TermDecl {
    pub name: String,
    pub reg: TermContent,
    pub data: Option<TermDeclData>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum TermDeclData {
    Ignore,
    Comment,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct RuleDecl {
    pub name: String,
    pub alternatives: Vec<RuleExpr>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum RuleExpr {
    Ref(RuleExprRef),
    Node(NodeRuleExpr),
}

impl RuleExpr {
    pub fn as_mut_node(&mut self) -> Option<&mut NodeRuleExpr> {
        match self {
            RuleExpr::Node(n) => Some(n),
            _ => None,
        }
    }

    pub fn as_node(&self) -> Option<&NodeRuleExpr> {
        match self {
            RuleExpr::Node(n) => Some(n),
            _ => None,
        }
    }

    pub fn as_ref(&self) -> Option<&RuleExprRef> {
        match self {
            RuleExpr::Ref(r) => Some(r),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct RuleExprRef {
    pub rule_name: String,
}

impl RuleExprRef {
    pub fn rule_name(&self) -> &str {
        &self.rule_name
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct NodeRuleExpr {
    pub prec: Option<AlternativePrecedence>,
    pub node_type: String,
    pub comps: Vec<AlternativeComp>,
}

impl NodeRuleExpr {
    pub fn node_type(&self) -> &str {
        &self.node_type
    }

    pub fn associativity(&self) -> Option<Associativity> {
        match self.prec? {
            AlternativePrecedence::Assoc(a) | AlternativePrecedence::Both(_, a) => Some(a),
            _ => None,
        }
    }

    pub fn precedence(&self) -> Option<usize> {
        match self.prec? {
            AlternativePrecedence::Prec(p) | AlternativePrecedence::Both(p, _) => Some(p),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum AlternativePrecedence {
    Prec(usize),
    Assoc(Associativity),
    Both(usize, Associativity),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Associativity {
    Left,
    Right,
}

// TODO: rename
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum AlternativeComp {
    Full(String, CompExpr),
    RuleRef(String),
    TExpr(TermExpr),
}

impl AlternativeComp {
    pub fn as_full(&self) -> Option<(&String, &CompExpr)> {
        match self {
            AlternativeComp::Full(s, c) => Some((s, c)),
            _ => None,
        }
    }

    pub fn references_nonterm_in(&self, targets: &[&str]) -> bool {
        matches!(self, AlternativeComp::Full(_, CompExpr::Some(n) | CompExpr::Opt(n) | CompExpr::Many(n) | CompExpr::Ref(n)) | AlternativeComp::RuleRef(n) if targets.contains(&n.as_str()))
    }
}

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum TermExpr {
    Ref(String),
    Content(TermContent),
    Alts(Vec<AltLevelTermExpr>),
}

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum AltLevelTermExpr {
    Ref(String),
    Content(TermContent),
}

impl AltLevelTermExpr {
    pub fn as_term_content(&self) -> Option<&TermContent> {
        match self {
            AltLevelTermExpr::Content(c) => Some(c),
            _ => None,
        }
    }

    pub fn as_str(&self) -> &str {
        match self {
            AltLevelTermExpr::Content(c) => c.as_str(),
            AltLevelTermExpr::Ref(r) => r.as_str(),
        }
    }
}

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum CompExpr {
    Ref(String),
    Many(String),
    Some(String),
    Opt(String),
    SepBy(SepByData),
}

impl CompExpr {
    pub fn as_nonterm_ref(&self) -> Option<&str> {
        match self {
            CompExpr::Ref(r) => Some(r),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct SepByData {
    pub allow_empty: bool,
    pub term: TermExpr,
    pub rule_name: String,
    pub trailing: bool,
}

#[derive(Debug, Clone)]
pub enum TermContent {
    Regex(fancy_regex::Regex),
    Literal(fancy_regex::Regex),
    Nested(fancy_regex::Regex, fancy_regex::Regex),
}

impl TermContent {
    pub fn regex(&self) -> &fancy_regex::Regex {
        match self {
            TermContent::Regex(r) => r,
            TermContent::Literal(l) => l,
            TermContent::Nested(start, _) => start,
        }
    }

    pub fn as_str(&self) -> &str {
        self.regex().as_str()
    }
}

impl PartialEq<Self> for TermContent {
    fn eq(&self, other: &Self) -> bool {
        self.regex().as_str().eq(other.regex().as_str())
    }
}

impl Eq for TermContent {}

impl Hash for TermContent {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write(self.regex().as_str().as_bytes())
    }
}

pub fn parse_meta_file(path: impl AsRef<str>) -> MetaParserRes<Vec<Decl>> {
    parse(&read_to_string(Path::new(path.as_ref()))?)
}

pub fn parse(input: &str) -> MetaParserRes<Vec<Decl>> {
    main(
        (MetaParser::parse(Rule::main, input)?)
            .next_child()?
            .into_inner(),
    )
}

fn main(pairs: Pairs<Rule>) -> MetaParserRes<Vec<Decl>> {
    pairs
        .filter(|p| p.as_rule() != Rule::EOI)
        .map(main_sub)
        .collect()
}

fn main_sub(pair: Pair<Rule>) -> MetaParserRes<Decl> {
    let res = match pair.as_rule() {
        Rule::terminal => Decl::Terminal(terminal(pair.into_inner(), None)?),
        Rule::ignore_terminal => {
            Decl::Terminal(terminal(pair.into_inner(), Some(TermDeclData::Ignore))?)
        }
        Rule::comment_terminal => {
            Decl::Terminal(terminal(pair.into_inner(), Some(TermDeclData::Comment))?)
        }
        Rule::node_decl => Decl::Node(node_decl(pair.into_inner())?),
        Rule::rule_decl => Decl::Rule(rule_decl(pair.into_inner())?),
        r => unexpected_rule(r, vec![Rule::terminal, Rule::node_decl, Rule::rule_decl])?,
    };
    Ok(res)
}

fn rule_decl(mut pairs: Pairs<Rule>) -> MetaParserRes<RuleDecl> {
    let name = t_name(pairs.next_child()?);
    let mut alternatives = vec![rule_expr(pairs.next_child()?.into_inner())?];
    let next_alternatives = pairs
        .map(|ps| rule_expr(ps.into_inner()))
        .collect::<MetaParserRes<Vec<RuleExpr>>>()?;
    alternatives.extend(next_alternatives);

    Ok(RuleDecl { name, alternatives })
}

fn rule_expr(mut pairs: Pairs<Rule>) -> MetaParserRes<RuleExpr> {
    let child = pairs.next_child()?;

    match child.as_rule() {
        Rule::rule_expr_ref => Ok(RuleExpr::Ref(rule_expr_ref(child.into_inner())?)),
        Rule::rule_expr_node => Ok(RuleExpr::Node(rule_expr_node(child.into_inner())?)),
        r => unexpected_rule(r, vec![Rule::rule_expr_ref, Rule::rule_expr_node])?,
    }
}

fn rule_expr_ref(mut pairs: Pairs<Rule>) -> MetaParserRes<RuleExprRef> {
    Ok(RuleExprRef {
        rule_name: t_name(pairs.next_child()?),
    })
}

fn rule_expr_node(mut pairs: Pairs<Rule>) -> MetaParserRes<NodeRuleExpr> {
    let precedence = if pairs.peek().map(|p| p.as_rule()) == Some(Rule::node_expr_precedence) {
        alternative_precedence(pairs.next_child()?.into_inner())
    } else {
        None
    };

    let node_type = t_name(pairs.next_child()?);

    let comps = pairs
        .map(alternative_comp)
        .collect::<MetaParserRes<Vec<AlternativeComp>>>()?;

    Ok(NodeRuleExpr {
        prec: precedence,
        node_type,
        comps,
    })
}

fn alternative_precedence(pairs: Pairs<Rule>) -> Option<AlternativePrecedence> {
    match (
        raw_precedence(pairs.clone()),
        raw_associativity(pairs.clone()),
    ) {
        (Some(p), Some(a)) => Some(AlternativePrecedence::Both(p, a)),
        (None, Some(a)) => Some(AlternativePrecedence::Assoc(a)),
        (Some(p), None) => Some(AlternativePrecedence::Prec(p)),
        _ => None,
    }
}

fn raw_precedence(mut pairs: Pairs<Rule>) -> Option<usize> {
    pairs.find(|p| p.as_rule() == Rule::int_literal).map(|p| {
        p.as_str()
            .parse()
            .unwrap_or_else(|_| panic!("Should be a valid usize: {}", p.as_str()))
    })
}

fn raw_associativity(mut pairs: Pairs<Rule>) -> Option<Associativity> {
    pairs
        .find(|p| p.as_rule() == Rule::alternative_associativity)
        .map(|p| {
            if p.as_str() == "left" {
                Associativity::Left
            } else {
                Associativity::Right
            }
        })
}

fn alternative_quantified_comp(mut pairs: Pairs<Rule>) -> MetaParserRes<AlternativeComp> {
    let binding = pairs.next_child()?.as_str().into();
    let ref_name = pairs.next_child()?.as_str().into();

    let quantifed_comp = match pairs.next().map(|p| p.as_str()) {
        Some("?") => CompExpr::Opt(ref_name),
        Some("*") => CompExpr::Many(ref_name),
        Some("+") => CompExpr::Some(ref_name),
        Some(other) => panic!("Invalid quantifier: {other}"),
        None => CompExpr::Ref(ref_name),
    };

    Ok(AlternativeComp::Full(binding, quantifed_comp))
}

fn alternative_op_comp(mut pairs: Pairs<Rule>) -> MetaParserRes<AlternativeComp> {
    let binding = pairs.next_child()?.as_str().into();
    let expr = comp_expr(pairs.next_child()?)?;
    Ok(AlternativeComp::Full(binding, expr))
}

fn comp_expr(pair: Pair<Rule>) -> MetaParserRes<CompExpr> {
    match pair.as_rule() {
        Rule::identifier => Ok(CompExpr::Ref(pair.as_str().into())),
        Rule::many_comp => Ok(CompExpr::Many(
            pair.into_inner().next_child()?.as_str().to_string(),
        )),
        Rule::some_comp => Ok(CompExpr::Some(
            pair.into_inner().next_child()?.as_str().to_string(),
        )),
        Rule::opt_comp => Ok(CompExpr::Opt(
            pair.into_inner().next_child()?.as_str().to_string(),
        )),
        r @ (Rule::sep_by_comp
        | Rule::sep_by_tr_comp
        | Rule::sep_by_1_comp
        | Rule::sep_by_tr_1_comp) => {
            let mut childs = pair.into_inner();
            let term = term_expr(childs.next_child()?.into_inner())?;
            let rule_name = childs.next_child()?.as_str().into();
            let allow_empty = matches!(r, Rule::sep_by_comp | Rule::sep_by_tr_comp);
            let trailing = matches!(r, Rule::sep_by_tr_comp | Rule::sep_by_tr_1_comp);
            Ok(CompExpr::SepBy(SepByData {
                allow_empty,
                term,
                rule_name,
                trailing,
            }))
        }
        r => unexpected_rule(r, vec![Rule::identifier, Rule::sep_by_comp])?,
    }
}

fn alternative_comp(pair: Pair<Rule>) -> MetaParserRes<AlternativeComp> {
    let res = match pair.as_rule() {
        Rule::term_expr => AlternativeComp::TExpr(term_expr(pair.into_inner())?),
        Rule::identifier => AlternativeComp::RuleRef(t_name(pair)),
        Rule::alternative_quantified_comp => alternative_quantified_comp(pair.into_inner())?,
        Rule::alternative_op_comp => alternative_op_comp(pair.into_inner())?,
        r => unexpected_rule(
            r,
            vec![
                Rule::term_content_regex,
                Rule::identifier,
                Rule::alternative_quantified_comp,
                Rule::alternative_op_comp,
            ],
        )?,
    };
    Ok(res)
}

fn term_expr(mut pairs: Pairs<Rule>) -> MetaParserRes<TermExpr> {
    let child = pairs.next_child()?;

    let res = match child.as_rule() {
        Rule::term_content => TermExpr::Content(term_content(child.into_inner())?),
        Rule::term_name => TermExpr::Ref(child.as_str().into()),
        Rule::term_alts => {
            let alts: Vec<AltLevelTermExpr> = child
                .into_inner()
                .map(alt_level_term_expr)
                .collect::<MetaParserRes<_>>()?;

            TermExpr::Alts(alts)
        }
        r => unexpected_rule(
            r,
            vec![Rule::term_content, Rule::term_name, Rule::term_alts],
        )?,
    };

    Ok(res)
}

fn alt_level_term_expr(pair: Pair<Rule>) -> MetaParserRes<AltLevelTermExpr> {
    let res = match pair.as_rule() {
        Rule::term_content => AltLevelTermExpr::Content(term_content(pair.into_inner())?),
        Rule::term_name => AltLevelTermExpr::Ref(pair.as_str().into()),
        r => unexpected_rule(r, vec![Rule::term_content, Rule::term_name])?,
    };

    Ok(res)
}

fn node_decl(mut pairs: Pairs<Rule>) -> MetaParserRes<NodeDecl> {
    let name = t_name(pairs.next_child()?);

    let parent_type = match pairs.peek().map(|p| p.as_rule()) {
        Some(Rule::type_name) => Some(t_name(pairs.next_child()?)),
        _ => None,
    };

    let fields = pairs
        .map(|ps| {
            let mut childs = ps.into_inner();
            let field_name = t_name(childs.next_child()?);
            let field_type = type_lit(childs.next_child()?.into_inner())?;
            Ok((field_name, field_type))
        })
        .collect::<MetaParserRes<BTreeMap<String, TypeLit>>>()?;

    Ok(NodeDecl {
        name,
        parent_type,
        fields,
    })
}

fn type_lit(mut pairs: Pairs<Rule>) -> MetaParserRes<TypeLit> {
    let first = type_lit_simple(pairs.next_child()?.into_inner())?;

    let following = pairs
        .map(|p| type_lit_simple(p.into_inner()))
        .collect::<MetaParserRes<Vec<SimpleTypeLit>>>()?;

    if following.is_empty() {
        Ok(TypeLit::Simple(first))
    } else {
        Ok(TypeLit::Or(OrTypeLit {
            alts: NonEmpty::from((first, following)),
        }))
    }
}

fn type_lit_simple(mut pairs: Pairs<Rule>) -> MetaParserRes<SimpleTypeLit> {
    Ok(SimpleTypeLit {
        name: t_name(pairs.next_child()?),
        parameters: pairs
            .map(|ps| type_lit(ps.into_inner()))
            .collect::<MetaParserRes<Vec<TypeLit>>>()?,
    })
}

fn terminal(mut pairs: Pairs<Rule>, data: Option<TermDeclData>) -> MetaParserRes<TermDecl> {
    let name = t_name(pairs.next_child()?);
    let reg = term_content(pairs.next_child()?.into_inner())?;
    Ok(TermDecl { name, reg, data })
}

fn t_name(pairs: Pair<Rule>) -> String {
    pairs.as_str().trim().into()
}

pub(crate) fn term_content(mut pairs: Pairs<Rule>) -> MetaParserRes<TermContent> {
    let child = pairs.next_child()?;

    match child.as_rule() {
        Rule::term_content_regex | Rule::term_content_literal => {
            term_regex_or_literal(child.into_inner())
        }
        Rule::term_content_call => term_content_call(child.into_inner()),
        r => unexpected_rule(
            r,
            vec![
                Rule::term_content_regex,
                Rule::term_content_literal,
                Rule::term_content_call,
            ],
        )?,
    }
}

fn term_regex_or_literal(mut pairs: Pairs<Rule>) -> MetaParserRes<TermContent> {
    let grand_child = pairs.next_child()?;
    // Remove escape char before backticks...
    let term_content_str = grand_child.as_str().replace(r#"\`"#, "`");

    let content = match grand_child.as_rule() {
        Rule::term_content_regex_inner => {
            let regex = fancy_regex::Regex::new(term_content_str.as_str())?;
            TermContent::Regex(regex)
        }
        Rule::term_content_literal_inner => {
            let regex = fancy_regex::Regex::new(&fancy_regex::escape(term_content_str.as_str()))?;
            TermContent::Literal(regex)
        }
        r => unexpected_rule(
            r,
            vec![
                Rule::term_content_regex_inner,
                Rule::term_content_literal_inner,
            ],
        )?,
    };

    Ok(content)
}

fn term_content_call(mut pairs: Pairs<Rule>) -> MetaParserRes<TermContent> {
    let call_name = pairs.next_child()?.as_str().to_string();
    let args = term_call_args(pairs);

    match call_name.as_str() {
        "nested" => {
            let start = term_regex_or_literal(read_arg(&args, "start")?.clone())?
                .regex()
                .clone();
            let end = term_regex_or_literal(read_arg(&args, "end")?.clone())?
                .regex()
                .clone();
            Ok(TermContent::Nested(start, end))
        }
        _ => Err(MetaParserErr::UnknownTermType(call_name)),
    }
}

fn term_call_args(mut pairs: Pairs<Rule>) -> HashMap<String, Pairs<Rule>> {
    pairs
        .next()
        .unwrap()
        .into_inner()
        .map(|p| {
            let mut childs = p.into_inner();
            let name = childs.next().unwrap().as_str().to_string();
            let value = childs.next().unwrap().into_inner();
            (name, value)
        })
        .collect()
}

fn read_arg<'a>(
    args: &'a HashMap<String, Pairs<Rule>>,
    name: &str,
) -> MetaParserRes<&'a Pairs<'a, Rule>> {
    args.get(name)
        .ok_or_else(|| MetaParserErr::MissingArgument(name.to_string()))
}

#[cfg(test)]
pub mod test {
    use indoc::indoc;
    use maplit::*;

    use crate::test::{parse_term_content, test_parser};

    use super::*;

    #[test]
    fn term_content_literal() {
        test_parser(
            MetaParser::parse(Rule::term_content, "'+'"),
            term_content,
            TermContent::Literal(fancy_regex::Regex::new(&fancy_regex::escape("+")).unwrap()),
        )
    }

    #[test]
    fn term_content_regex() {
        test_parser(
            MetaParser::parse(Rule::term_content, "`a+`"),
            term_content,
            TermContent::Regex(fancy_regex::Regex::new("a+").unwrap()),
        )
    }

    #[test]
    fn term_content_ignore_escaped_backticks() {
        test_parser(
            MetaParser::parse(Rule::term_content, r#"`\``"#),
            term_content,
            TermContent::Regex(fancy_regex::Regex::new("`").unwrap()),
        )
    }

    #[test]
    fn test_term_decl() {
        test_parser(
            MetaParser::parse(Rule::main, "term INT_LIT = `[0-9]+`"),
            main,
            vec![Decl::Terminal(TermDecl {
                name: "INT_LIT".into(),
                reg: parse_term_content("`[0-9]+`"),
                data: None,
            })],
        )
    }

    #[test]
    fn ignore_term() {
        test_parser(
            MetaParser::parse(Rule::main, "ignore term LINE_BREAK = '\\n'"),
            main,
            vec![Decl::Terminal(TermDecl {
                name: "LINE_BREAK".into(),
                reg: parse_term_content("'\\n'"),
                data: Some(TermDeclData::Ignore),
            })],
        )
    }

    #[test]
    fn comment_term() {
        test_parser(
            MetaParser::parse(Rule::main, "comment term LINE_COMMENT = `//.*\\n`"),
            main,
            vec![Decl::Terminal(TermDecl {
                name: "LINE_COMMENT".into(),
                reg: parse_term_content("`//.*\\n`"),
                data: Some(TermDeclData::Comment),
            })],
        )
    }

    #[test]
    fn nested_comment_term() {
        test_parser(
            MetaParser::parse(
                Rule::main,
                r#"comment term BLOCK_COMMENT = nested(start = '/*', end = '*/')"#,
            ),
            main,
            vec![Decl::Terminal(TermDecl {
                name: "BLOCK_COMMENT".into(),
                reg: TermContent::Nested(
                    fancy_regex::Regex::new(&fancy_regex::escape("/*")).unwrap(),
                    fancy_regex::Regex::new(&fancy_regex::escape("*/")).unwrap(),
                ),
                data: Some(TermDeclData::Comment),
            })],
        )
    }

    #[test]
    fn rule_with_term_ref() {
        let spec = indoc!(
            "term INT_LIT = `[0-9]+`
             rule main = IntLiteral { INT_LIT }
            "
        );

        test_parser(
            MetaParser::parse(Rule::main, spec),
            main,
            vec![
                Decl::Terminal(TermDecl {
                    name: "INT_LIT".into(),
                    reg: parse_term_content("`[0-9]+`"),
                    data: None,
                }),
                Decl::Rule(RuleDecl {
                    name: "main".into(),
                    alternatives: vec![RuleExpr::Node(NodeRuleExpr {
                        node_type: "IntLiteral".into(),
                        comps: vec![AlternativeComp::TExpr(TermExpr::Ref("INT_LIT".into()))],
                        prec: None,
                    })],
                }),
            ],
        );
    }

    #[test]
    fn term_expr_alts() {
        let spec = indoc!(
            "term A = 'a'
            rule main = Node { [A, `b`] }
            "
        );

        test_parser(
            MetaParser::parse(Rule::main, spec),
            main,
            vec![
                Decl::Terminal(TermDecl {
                    name: "A".into(),
                    reg: parse_term_content("'a'"),
                    data: None,
                }),
                Decl::Rule(RuleDecl {
                    name: "main".into(),
                    alternatives: vec![RuleExpr::Node(NodeRuleExpr {
                        node_type: "Node".into(),
                        prec: None,
                        comps: vec![AlternativeComp::TExpr(TermExpr::Alts(vec![
                            AltLevelTermExpr::Ref("A".into()),
                            AltLevelTermExpr::Content(parse_term_content("`b`")),
                        ]))],
                    })],
                }),
            ],
        )
    }

    #[test]
    fn test_node_with_parameterized_type() {
        test_parser(
            MetaParser::parse(Rule::node_decl, "node B { fields: List<A> }"),
            node_decl,
            NodeDecl {
                name: "B".into(),
                parent_type: None,
                fields: btreemap! {
                    "fields".into() =>
                        TypeLit::Simple(SimpleTypeLit {
                            name: "List".into(),
                            parameters: vec![TypeLit::Simple(SimpleTypeLit { name: "A".into(), parameters: vec![]})]
                        })
                },
            },
        )
    }

    #[test]
    fn test_node_decl() {
        let expr_type = TypeLit::Simple(SimpleTypeLit {
            name: "Expr".into(),
            parameters: vec![],
        });
        let op_type = TypeLit::Simple(SimpleTypeLit {
            name: "Op".into(),
            parameters: vec![],
        });

        test_parser(
            MetaParser::parse(
                Rule::node_decl,
                "node Binop: Expr { left: Expr, op: Op, right: Expr }",
            ),
            node_decl,
            NodeDecl {
                name: "Binop".into(),
                parent_type: Some("Expr".into()),
                fields: btreemap! {
                    "left".into() => expr_type.clone(),
                    "op".into() => op_type,
                    "right".into() => expr_type
                },
            },
        )
    }

    #[test]
    fn test_node_without_parent() {
        let type_type = TypeLit::Simple(SimpleTypeLit {
            name: "Type".into(),
            parameters: vec![],
        });

        test_parser(
            MetaParser::parse(Rule::node_decl, "node Binop { field_name: Type }"),
            node_decl,
            NodeDecl {
                name: "Binop".into(),
                parent_type: None,
                fields: btreemap! { "field_name".into() => type_type },
            },
        )
    }

    #[test]
    fn some_quant_comps() {
        test_parser(
            MetaParser::parse(Rule::alternative_quantified_comp, "arg@expr+"),
            alternative_quantified_comp,
            AlternativeComp::Full("arg".into(), CompExpr::Some("expr".into())),
        )
    }

    #[test]
    fn some_op_comps() {
        test_parser(
            MetaParser::parse(Rule::alternative_op_comp, "arg@some(expr)"),
            alternative_op_comp,
            AlternativeComp::Full("arg".into(), CompExpr::Some("expr".into())),
        )
    }

    #[test]
    fn many_quant_comps() {
        test_parser(
            MetaParser::parse(Rule::alternative_quantified_comp, "arg@expr*"),
            alternative_quantified_comp,
            AlternativeComp::Full("arg".into(), CompExpr::Many("expr".into())),
        )
    }

    #[test]
    fn many_op_comps() {
        test_parser(
            MetaParser::parse(Rule::alternative_op_comp, "arg@many(expr)"),
            alternative_op_comp,
            AlternativeComp::Full("arg".into(), CompExpr::Many("expr".into())),
        )
    }

    #[test]
    fn opt_quant_comps() {
        test_parser(
            MetaParser::parse(Rule::alternative_quantified_comp, "arg@expr?"),
            alternative_quantified_comp,
            AlternativeComp::Full("arg".into(), CompExpr::Opt("expr".into())),
        )
    }

    #[test]
    fn opt_op_comps() {
        test_parser(
            MetaParser::parse(Rule::alternative_op_comp, "arg@opt(expr)"),
            alternative_op_comp,
            AlternativeComp::Full("arg".into(), CompExpr::Opt("expr".into())),
        )
    }

    #[test]
    fn sep_by_comp_expr() {
        test_parser(
            MetaParser::parse(Rule::alternative_op_comp, "args@sepBy(',', arg)"),
            alternative_op_comp,
            AlternativeComp::Full(
                "args".into(),
                CompExpr::SepBy(SepByData {
                    allow_empty: true,
                    term: TermExpr::Content(TermContent::Literal(
                        fancy_regex::Regex::new(",").unwrap(),
                    )),
                    rule_name: "arg".into(),
                    trailing: false,
                }),
            ),
        )
    }

    #[test]
    fn sep_by_tr_comp_expr() {
        test_parser(
            MetaParser::parse(Rule::alternative_op_comp, "args@sepByTr(',', arg)"),
            alternative_op_comp,
            AlternativeComp::Full(
                "args".into(),
                CompExpr::SepBy(SepByData {
                    allow_empty: true,
                    term: TermExpr::Content(TermContent::Literal(
                        fancy_regex::Regex::new(",").unwrap(),
                    )),
                    rule_name: "arg".into(),
                    trailing: true,
                }),
            ),
        )
    }

    #[test]
    fn sep_by_1_comp_expr() {
        test_parser(
            MetaParser::parse(Rule::alternative_op_comp, "args@sepBy1(',', arg)"),
            alternative_op_comp,
            AlternativeComp::Full(
                "args".into(),
                CompExpr::SepBy(SepByData {
                    allow_empty: false,
                    term: TermExpr::Content(TermContent::Literal(
                        fancy_regex::Regex::new(",").unwrap(),
                    )),
                    rule_name: "arg".into(),
                    trailing: false,
                }),
            ),
        )
    }

    #[test]
    fn sep_by_tr_1_comp_expr() {
        test_parser(
            MetaParser::parse(Rule::alternative_op_comp, "args@sepByTr1(',', arg)"),
            alternative_op_comp,
            AlternativeComp::Full(
                "args".into(),
                CompExpr::SepBy(SepByData {
                    allow_empty: false,
                    term: TermExpr::Content(TermContent::Literal(
                        fancy_regex::Regex::new(",").unwrap(),
                    )),
                    rule_name: "arg".into(),
                    trailing: true,
                }),
            ),
        )
    }

    #[test]
    fn test_rule_decl_single_comp() {
        test_parser(
            MetaParser::parse(Rule::rule_decl, "rule myRule = Node { 'hello' }"),
            rule_decl,
            RuleDecl {
                name: "myRule".into(),
                alternatives: vec![RuleExpr::Node(NodeRuleExpr {
                    prec: None,
                    node_type: "Node".into(),
                    comps: vec![AlternativeComp::TExpr(TermExpr::Content(
                        TermContent::Literal(fancy_regex::Regex::new("hello").unwrap()),
                    ))],
                })],
            },
        )
    }

    #[test]
    fn parameterized_type() {
        test_parser(
            MetaParser::parse(Rule::type_lit, "List<Node>"),
            type_lit,
            TypeLit::Simple(SimpleTypeLit {
                name: "List".into(),
                parameters: vec![TypeLit::Simple(SimpleTypeLit {
                    name: "Node".into(),
                    parameters: vec![],
                })],
            }),
        )
    }

    #[test]
    fn or_type() {
        test_parser(
            MetaParser::parse(Rule::type_lit, "Node1 | List<Node2 | Node1>"),
            type_lit,
            TypeLit::Or(OrTypeLit {
                alts: NonEmpty::from((
                    SimpleTypeLit {
                        name: "Node1".to_string(),
                        parameters: vec![],
                    },
                    vec![SimpleTypeLit {
                        name: "List".to_string(),
                        parameters: vec![TypeLit::Or(OrTypeLit {
                            alts: NonEmpty::from((
                                SimpleTypeLit {
                                    name: "Node2".to_string(),
                                    parameters: vec![],
                                },
                                vec![SimpleTypeLit {
                                    name: "Node1".to_string(),
                                    parameters: vec![],
                                }],
                            )),
                        })],
                    }],
                )),
            }),
        )
    }

    #[test]
    fn left_associativity() {
        test_parser(
            MetaParser::parse(Rule::node_expr_precedence, "[ left ]"),
            |pairs| {
                Ok(alternative_precedence(pairs).unwrap()) as MetaParserRes<AlternativePrecedence>
            },
            AlternativePrecedence::Assoc(Associativity::Left),
        )
    }

    #[test]
    fn right_associativity() {
        test_parser(
            MetaParser::parse(Rule::node_expr_precedence, "[right]"),
            |pairs| {
                Ok(alternative_precedence(pairs).unwrap()) as MetaParserRes<AlternativePrecedence>
            },
            AlternativePrecedence::Assoc(Associativity::Right),
        )
    }

    #[test]
    fn only_associativity() {
        test_parser(
            MetaParser::parse(Rule::node_expr_precedence, "[42]"),
            |pairs| {
                Ok(alternative_precedence(pairs).unwrap()) as MetaParserRes<AlternativePrecedence>
            },
            AlternativePrecedence::Prec(42),
        )
    }

    #[test]
    fn complete_precedence_spec() {
        test_parser(
            MetaParser::parse(Rule::node_expr_precedence, "[6,left]"),
            |pairs| {
                Ok(alternative_precedence(pairs).unwrap()) as MetaParserRes<AlternativePrecedence>
            },
            AlternativePrecedence::Both(6, Associativity::Left),
        )
    }

    #[test]
    fn test_rule_ref() {
        test_parser(
            MetaParser::parse(Rule::rule_decl, r"rule main = Unop { main } | alt_rule"),
            rule_decl,
            RuleDecl {
                name: "main".into(),
                alternatives: vec![
                    RuleExpr::Node(NodeRuleExpr {
                        prec: None,
                        node_type: "Unop".into(),
                        comps: vec![AlternativeComp::RuleRef("main".into())],
                    }),
                    RuleExpr::Ref(RuleExprRef {
                        rule_name: "alt_rule".into(),
                    }),
                ],
            },
        )
    }

    #[test]
    fn test_rule_decl() {
        test_parser(
            MetaParser::parse(
                Rule::rule_decl,
                r"rule expr = 
                        [6] Binop { expr '+' expr } 
                      | [left, 7] Binop { expr '-' expr }",
            ),
            rule_decl,
            RuleDecl {
                name: "expr".into(),
                alternatives: vec![
                    RuleExpr::Node(NodeRuleExpr {
                        prec: Some(AlternativePrecedence::Prec(6)),
                        node_type: "Binop".into(),
                        comps: vec![
                            AlternativeComp::RuleRef("expr".into()),
                            AlternativeComp::TExpr(TermExpr::Content(TermContent::Literal(
                                fancy_regex::Regex::new(&fancy_regex::escape("+")).unwrap(),
                            ))),
                            AlternativeComp::RuleRef("expr".into()),
                        ],
                    }),
                    RuleExpr::Node(NodeRuleExpr {
                        prec: Some(AlternativePrecedence::Both(7, Associativity::Left)),
                        node_type: "Binop".into(),
                        comps: vec![
                            AlternativeComp::RuleRef("expr".into()),
                            AlternativeComp::TExpr(TermExpr::Content(TermContent::Literal(
                                fancy_regex::Regex::new(&fancy_regex::escape("-")).unwrap(),
                            ))),
                            AlternativeComp::RuleRef("expr".into()),
                        ],
                    }),
                ],
            },
        )
    }
}
