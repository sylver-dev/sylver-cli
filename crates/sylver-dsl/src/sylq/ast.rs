use std::hash::{Hash, Hasher};

use pest::error::Error;
use pest::{
    iterators::{Pair, Pairs},
    Parser,
};
use pest_derive::*;
use thiserror::Error;

use derive_more::From;
use non_empty_vec::NonEmpty;

use crate::util::WalkError;

#[derive(Debug, Error)]
pub enum SylqParserError {
    #[error(transparent)]
    PestErr(Box<pest::error::Error<Rule>>),
    #[error(transparent)]
    Walk(#[from] WalkError<Rule>),
    #[error(transparent)]
    RegexErr(#[from] Box<fancy_regex::Error>),
}

impl From<pest::error::Error<Rule>> for SylqParserError {
    fn from(e: Error<Rule>) -> Self {
        SylqParserError::PestErr(Box::new(e))
    }
}

pub type SylqParserRes<T> = Result<T, SylqParserError>;

#[derive(Parser)]
#[grammar = "sylq/sylq.pest"]
pub struct SylqParser {}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct QueryPattern {
    pub node_pattern: NodePatternsWithBinding,
    pub predicate: Option<Expr>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct NodePatternsWithBinding {
    pub node_patterns: NonEmpty<NodePattern>,
    pub binding: Option<String>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct NodePattern {
    pub kind_pattern: KindPattern,
    pub fields: Vec<NodePatternField>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum KindPattern {
    KindName(String),
    Placeholder,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct NodePatternField {
    pub desc: NodePatternFieldDesc,
    pub value: NodePatternFieldValue,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum NodePatternFieldDesc {
    Identifier(String),
    Index(usize),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum NodePatternFieldValue {
    Pattern(QueryPattern),
    Text(String),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Expr {
    Identifier(String),
    SpecialIdentifier(String),
    Integer(i64),
    Null,
    StringLit(String),
    RegexLit(ExprRegex),
    DotAccess(bool, Box<Expr>, String),
    DotCall(bool, Box<Expr>, String, Vec<Arg>),
    Not(Box<Expr>),
    Binop(Box<Expr>, Op, Box<Expr>),
    Is(Box<Expr>, Box<QueryPattern>),
    ArrayIndex(Box<Expr>, Box<Expr>),
    ArrayQuant(ArrayQuantQuant, Box<Expr>, Box<QueryPattern>),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Arg {
    Named(String, Expr),
    Unnamed(Expr),
}

#[derive(Debug, Clone, From)]
pub struct ExprRegex(fancy_regex::Regex);

impl ExprRegex {
    pub fn is_match(&self, txt: &str) -> bool {
        let match_res = self.0.is_match(txt);
        matches!(match_res, Ok(true))
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl Hash for ExprRegex {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.as_str().hash(state)
    }
}

impl PartialEq<Self> for ExprRegex {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_str().eq(other.0.as_str())
    }
}

impl Eq for ExprRegex {}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Op {
    Lt,
    Lte,
    Ht,
    Hte,
    And,
    Or,
    EqEq,
    Neq,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum ArrayQuantQuant {
    No,
    Any,
    All,
}

pub fn parse_query(query_code: impl AsRef<str>) -> SylqParserRes<QueryPattern> {
    query(
        SylqParser::parse(Rule::query, query_code.as_ref())?
            .next()
            .unwrap()
            .into_inner(),
    )
}

pub fn parse_expr(expr_code: impl AsRef<str>) -> Expr {
    expr(
        SylqParser::parse(Rule::expr, expr_code.as_ref())
            .unwrap()
            .next()
            .unwrap()
            .into_inner(),
    )
    .unwrap()
}

fn query(mut pairs: Pairs<Rule>) -> SylqParserRes<QueryPattern> {
    let child = pairs.next().unwrap();

    match child.as_rule() {
        Rule::braced_query_pattern | Rule::query_pattern => query(child.into_inner()),
        Rule::query_pattern_simple | Rule::query_pattern_full => query_pattern(child.into_inner()),
        r => panic!("Unexpected rule {r:?}"),
    }
}

fn query_pattern(mut pairs: Pairs<Rule>) -> SylqParserRes<QueryPattern> {
    let pattern = node_pattern(pairs.next().unwrap().into_inner())?;
    let predicate = pairs
        .find(|p| p.as_rule() != Rule::EOI)
        .map(|p| expr(p.into_inner()))
        .transpose()?;

    Ok(QueryPattern {
        node_pattern: pattern,
        predicate,
    })
}

fn node_pattern(mut pairs: Pairs<Rule>) -> SylqParserRes<NodePatternsWithBinding> {
    let child = pairs.next().unwrap();

    match child.as_rule() {
        Rule::node_pattern_post_binding => node_pattern_post_binding(child.into_inner()),
        Rule::node_pattern_pre_binding => node_pattern_pre_binding(child.into_inner()),
        Rule::node_pattern => node_pattern(child.into_inner()),
        r => panic!("Unexpected rule {r:?}, expected node pattern"),
    }
}

fn node_pattern_post_binding(mut pairs: Pairs<Rule>) -> SylqParserRes<NodePatternsWithBinding> {
    let node_patterns = node_pattern_val(pairs.next().unwrap().into_inner())?;
    let binding = pairs.next().map(pair_text);

    Ok(NodePatternsWithBinding {
        node_patterns,
        binding,
    })
}

fn node_pattern_pre_binding(mut pairs: Pairs<Rule>) -> SylqParserRes<NodePatternsWithBinding> {
    let binding = pair_text(pairs.next().unwrap());
    let node_patterns = node_pattern_val(pairs.next().unwrap().into_inner())?;

    Ok(NodePatternsWithBinding {
        node_patterns,
        binding: Some(binding),
    })
}

fn node_pattern_val(mut pairs: Pairs<Rule>) -> SylqParserRes<NonEmpty<NodePattern>> {
    let first = node_pattern_val_raw(pairs.next().unwrap().into_inner())?;

    let rest = pairs
        .map(|p| node_pattern_val_raw(p.into_inner()))
        .collect::<SylqParserRes<Vec<NodePattern>>>()?;

    Ok(NonEmpty::from((first, rest)))
}

fn node_pattern_val_raw(mut pairs: Pairs<Rule>) -> SylqParserRes<NodePattern> {
    let kind_pattern = node_pattern_val_pattern(pairs.next().unwrap());

    let fields = pairs
        .map(|p| node_pattern_val_field(p.into_inner()))
        .collect::<SylqParserRes<Vec<NodePatternField>>>()?;

    Ok(NodePattern {
        kind_pattern,
        fields,
    })
}

fn node_pattern_val_pattern(pair: Pair<Rule>) -> KindPattern {
    match pair.as_rule() {
        Rule::identifier | Rule::list_kind => KindPattern::KindName(pair_text(pair)),
        Rule::placeholder => KindPattern::Placeholder,
        r => panic!("Unexpected rule {r:?}, expected list kind, identifier or placeholder"),
    }
}

fn node_pattern_val_field(mut pairs: Pairs<Rule>) -> SylqParserRes<NodePatternField> {
    let desc = node_pattern_field_desc(pairs.next().unwrap());

    let value_pair = pairs.next().unwrap();

    let value = match value_pair.as_rule() {
        Rule::string_literal => NodePatternFieldValue::Text(string_literal(value_pair)?),
        Rule::query_pattern => NodePatternFieldValue::Pattern(query_pattern(
            value_pair.into_inner().next().unwrap().into_inner(),
        )?),
        r => panic!("Unexpected rule {r:?}, expected query pattern or string literal"),
    };

    Ok(NodePatternField { desc, value })
}

fn node_pattern_field_desc(pair: Pair<Rule>) -> NodePatternFieldDesc {
    match pair.as_rule() {
        Rule::identifier => NodePatternFieldDesc::Identifier(pair_text(pair)),
        Rule::node_pattern_val_field_index => {
            NodePatternFieldDesc::Index(pair.into_inner().next().unwrap().as_str().parse().unwrap())
        }
        r => panic!("Unexpected rule {r:?}, expected identifier or placeholder"),
    }
}

fn expr(mut pairs: Pairs<Rule>) -> SylqParserRes<Expr> {
    let child = pairs.next().unwrap();

    match child.as_rule() {
        Rule::special_identifier => Ok(Expr::SpecialIdentifier(pair_text(child))),
        Rule::identifier => Ok(Expr::Identifier(pair_text(child))),
        Rule::integer => integer(child),
        Rule::null => Ok(Expr::Null),
        Rule::string_literal => Ok(Expr::StringLit(string_literal(child)?)),
        Rule::bin_op | Rule::bin_log_op => binop(child.into_inner()),
        Rule::primary_op | Rule::cmp_expr | Rule::atomic_expr | Rule::expr => {
            expr(child.into_inner())
        }
        Rule::term => term(child.into_inner()),
        Rule::is_expr => is_expr(child.into_inner()),
        Rule::array_index => array_index(child.into_inner()),
        Rule::array_quant_expr => array_quant(child.into_inner()),
        Rule::regex_literal => regex_literal(child.into_inner()),
        Rule::not_expr => not_expr(child.into_inner()),
        r => panic!("Unexpected rule: {r:?}"),
    }
}

fn integer(pair: Pair<Rule>) -> SylqParserRes<Expr> {
    Ok(Expr::Integer(pair.as_str().parse().unwrap()))
}

fn string_literal(pair: Pair<Rule>) -> SylqParserRes<String> {
    let txt = pair.as_str().to_string();
    let quote = txt.chars().next().unwrap();

    let stripped = (txt[1..txt.len() - 1]).replace(&format!("\\{quote}"), &quote.to_string());

    Ok(stripped)
}

fn is_expr(mut pairs: Pairs<Rule>) -> SylqParserRes<Expr> {
    let operand = expr(pairs.next().unwrap().into_inner())?;
    let pattern = query(pairs.next().unwrap().into_inner())?;
    Ok(Expr::Is(Box::new(operand), Box::new(pattern)))
}

fn array_index(mut pairs: Pairs<Rule>) -> SylqParserRes<Expr> {
    let array = expr(pairs.next().unwrap().into_inner())?;
    let index = expr(pairs.next().unwrap().into_inner())?;
    Ok(Expr::ArrayIndex(Box::new(array), Box::new(index)))
}

fn array_quant(mut pairs: Pairs<Rule>) -> SylqParserRes<Expr> {
    let quant = array_quant_quant(pairs.next().unwrap());
    let origin = expr(pairs.next().unwrap().into_inner())?;
    let pattern = query(pairs.next().unwrap().into_inner())?;
    Ok(Expr::ArrayQuant(quant, Box::new(origin), Box::new(pattern)))
}

fn regex_literal(mut pairs: Pairs<Rule>) -> SylqParserRes<Expr> {
    let regex_txt = pairs.next().unwrap().as_str().replace(r#"\`"#, "`");

    fancy_regex::Regex::new(&regex_txt)
        .map(|r| Expr::RegexLit(ExprRegex(r)))
        .map_err(|err| SylqParserError::RegexErr(Box::new(err)))
}

fn not_expr(mut pairs: Pairs<Rule>) -> SylqParserRes<Expr> {
    expr(pairs.next().unwrap().into_inner()).map(|e| Expr::Not(Box::new(e)))
}

fn array_quant_quant(pair: Pair<Rule>) -> ArrayQuantQuant {
    match pair.as_str() {
        "no" => ArrayQuantQuant::No,
        "any" => ArrayQuantQuant::Any,
        "all" => ArrayQuantQuant::All,
        q => panic!("Invalid quantifier: {q}"),
    }
}

fn binop(mut pairs: Pairs<Rule>) -> SylqParserRes<Expr> {
    let left = expr(pairs.next().unwrap().into_inner())?;
    let op = op(pairs.next().unwrap())?;
    let right = expr(pairs.next().unwrap().into_inner())?;

    Ok(Expr::Binop(Box::new(left), op, Box::new(right)))
}

fn term(mut pairs: Pairs<Rule>) -> SylqParserRes<Expr> {
    let mut current_expr = expr(pairs.next().unwrap().into_inner())?;

    for p in pairs {
        match p.as_rule() {
            Rule::dot_access_suffix => {
                current_expr = dot_access_suffix(current_expr, p.into_inner());
            }
            Rule::array_index_suffix => {
                let index_expr = expr(p.into_inner())?;
                current_expr = Expr::ArrayIndex(Box::new(current_expr), Box::new(index_expr));
            }
            Rule::dot_call_suffix => {
                let mut childs = p.into_inner();
                let safe = is_safe_dot(childs.next().unwrap());

                let mut call_childs = childs.next().unwrap().into_inner();
                let callee_name = call_childs.next().unwrap().as_str().to_string();

                let args = if let Some(arg_pairs) = call_childs.next() {
                    arg_pairs
                        .into_inner()
                        .map(arg)
                        .collect::<SylqParserRes<Vec<Arg>>>()?
                } else {
                    vec![]
                };

                current_expr = Expr::DotCall(safe, Box::new(current_expr), callee_name, args);
            }
            r => {
                panic!(
                    "Invalid rule: {r:?}, expected one of: dot_access_suffix, array_index_suffix"
                );
            }
        }
    }

    Ok(current_expr)
}

fn arg(arg: Pair<Rule>) -> SylqParserRes<Arg> {
    match arg.as_rule() {
        Rule::unnamed_arg => Ok(Arg::Unnamed(expr(arg.into_inner())?)),
        Rule::named_arg => {
            let mut childs = arg.into_inner();
            let name = childs.next().unwrap().as_str().to_string();
            let value = expr(childs.next().unwrap().into_inner())?;
            Ok(Arg::Named(name, value))
        }
        r => {
            panic!("Invalid rule: {r:?}, expected one of: named_arg, unnamed_arg");
        }
    }
}

fn dot_access_suffix(current_expr: Expr, mut pairs: Pairs<Rule>) -> Expr {
    let safe = is_safe_dot(pairs.next().unwrap());
    let name = pairs.next().unwrap().as_str().to_string();
    Expr::DotAccess(safe, Box::new(current_expr), name)
}

fn is_safe_dot(pair: Pair<Rule>) -> bool {
    matches!(pair.as_rule(), Rule::dot_op_safe)
}

fn op(pair: Pair<Rule>) -> SylqParserRes<Op> {
    let op = match pair.as_str() {
        "<" => Op::Lt,
        "<=" => Op::Lte,
        ">" => Op::Ht,
        ">=" => Op::Hte,
        "&&" => Op::And,
        "||" => Op::Or,
        "==" => Op::EqEq,
        "!=" => Op::Neq,
        o => panic!("Invalid operator: {o}"),
    };

    Ok(op)
}

fn pair_text(pair: Pair<Rule>) -> String {
    pair.as_str().trim().into()
}

#[cfg(test)]
pub mod test {
    use fancy_regex::Regex;

    use crate::test::test_parser;

    use super::*;

    #[test]
    fn special_identifier() {
        test_parser(
            SylqParser::parse(Rule::expr, "$125"),
            expr,
            Expr::SpecialIdentifier("$125".to_string()),
        );
    }

    #[test]
    fn null() {
        test_parser(SylqParser::parse(Rule::expr, "null"), expr, Expr::Null);
    }

    #[test]
    fn not_expr() {
        test_parser(
            SylqParser::parse(Rule::expr, "!boolValue"),
            expr,
            Expr::Not(Box::new(Expr::Identifier("boolValue".to_string()))),
        );
    }

    #[test]
    fn double_string_literal() {
        test_parser(
            SylqParser::parse(Rule::expr, r#""hello""#),
            expr,
            Expr::StringLit("hello".to_string()),
        )
    }

    #[test]
    fn double_escaped_string_literal() {
        test_parser(
            SylqParser::parse(Rule::expr, "\"hell\\\"o\""),
            expr,
            Expr::StringLit(r#"hell"o"#.to_string()),
        )
    }

    #[test]
    fn simple_string_literal() {
        test_parser(
            SylqParser::parse(Rule::expr, "'hello'"),
            expr,
            Expr::StringLit("hello".to_string()),
        )
    }

    #[test]
    fn simple_escaped_string_literal() {
        test_parser(
            SylqParser::parse(Rule::expr, "'hell\\'o'"),
            expr,
            Expr::StringLit(r#"hell'o"#.to_string()),
        )
    }

    #[test]
    fn neq_operator() {
        test_parser(
            SylqParser::parse(Rule::expr, "10 != 9"),
            expr,
            Expr::Binop(
                Box::new(Expr::Integer(10)),
                Op::Neq,
                Box::new(Expr::Integer(9)),
            ),
        )
    }

    #[test]
    fn regex_literal() {
        test_parser(
            SylqParser::parse(Rule::expr, "`hello`"),
            expr,
            Expr::RegexLit(ExprRegex(Regex::new("hello").unwrap())),
        )
    }

    #[test]
    fn expr_in_par() {
        test_parser(SylqParser::parse(Rule::expr, "(1)"), expr, Expr::Integer(1))
    }

    #[test]
    fn array_index() {
        test_parser(
            SylqParser::parse(Rule::expr, "children[0]"),
            expr,
            Expr::ArrayIndex(
                Box::new(Expr::Identifier("children".to_string())),
                Box::new(Expr::Integer(0)),
            ),
        )
    }

    #[test]
    fn safe_dot_access() {
        test_parser(
            SylqParser::parse(Rule::expr, "node?.field"),
            expr,
            Expr::DotAccess(
                true,
                Box::new(Expr::Identifier("node".to_string())),
                "field".to_string(),
            ),
        )
    }

    #[test]
    fn dot_call() {
        test_parser(
            SylqParser::parse(Rule::expr, "node.call(1)"),
            expr,
            Expr::DotCall(
                false,
                Box::new(Expr::Identifier("node".to_string())),
                "call".to_string(),
                vec![Arg::Unnamed(Expr::Integer(1))],
            ),
        )
    }

    #[test]
    fn safe_dot_call() {
        test_parser(
            SylqParser::parse(Rule::expr, "node?.call(1)"),
            expr,
            Expr::DotCall(
                true,
                Box::new(Expr::Identifier("node".to_string())),
                "call".to_string(),
                vec![Arg::Unnamed(Expr::Integer(1))],
            ),
        )
    }

    #[test]
    fn dot_access_index_interlace() {
        test_parser(
            SylqParser::parse(Rule::expr, "node.prop1[0].prop2"),
            expr,
            Expr::DotAccess(
                false,
                Box::new(Expr::ArrayIndex(
                    Box::new(Expr::DotAccess(
                        false,
                        Box::new(Expr::Identifier("node".to_string())),
                        "prop1".to_string(),
                    )),
                    Box::new(Expr::Integer(0)),
                )),
                "prop2".to_string(),
            ),
        )
    }

    #[test]
    fn array_quant_expr() {
        test_parser(
            SylqParser::parse(Rule::expr, "any n.children match { Node }"),
            expr,
            Expr::ArrayQuant(
                ArrayQuantQuant::Any,
                Box::new(Expr::DotAccess(
                    false,
                    Box::new(Expr::Identifier("n".to_string())),
                    "children".to_string(),
                )),
                Box::new(QueryPattern {
                    node_pattern: NodePatternsWithBinding {
                        binding: None,
                        node_patterns: NonEmpty::new(NodePattern {
                            kind_pattern: KindPattern::KindName("Node".to_string()),
                            fields: vec![],
                        }),
                    },
                    predicate: None,
                }),
            ),
        )
    }

    #[test]
    fn array_quant_expr_with_predicate() {
        test_parser(
            SylqParser::parse(Rule::expr, "any n.children match { _ c when value }"),
            expr,
            Expr::ArrayQuant(
                ArrayQuantQuant::Any,
                Box::new(Expr::DotAccess(
                    false,
                    Box::new(Expr::Identifier("n".to_string())),
                    "children".to_string(),
                )),
                Box::new(QueryPattern {
                    node_pattern: NodePatternsWithBinding {
                        binding: Some("c".to_string()),
                        node_patterns: NonEmpty::new(NodePattern {
                            kind_pattern: KindPattern::Placeholder,
                            fields: vec![],
                        }),
                    },
                    predicate: Some(Expr::Identifier("value".to_string())),
                }),
            ),
        )
    }

    #[test]
    fn ht_operator() {
        test_parser(
            SylqParser::parse(Rule::expr, "10 > 9"),
            expr,
            Expr::Binop(
                Box::new(Expr::Integer(10)),
                Op::Ht,
                Box::new(Expr::Integer(9)),
            ),
        )
    }

    #[test]
    fn hte_operator() {
        test_parser(
            SylqParser::parse(Rule::expr, "10 >= 9"),
            expr,
            Expr::Binop(
                Box::new(Expr::Integer(10)),
                Op::Hte,
                Box::new(Expr::Integer(9)),
            ),
        )
    }

    #[test]
    fn and_operator() {
        test_parser(
            SylqParser::parse(Rule::expr, "var1 && var2"),
            expr,
            Expr::Binop(
                Box::new(Expr::Identifier("var1".to_string())),
                Op::And,
                Box::new(Expr::Identifier("var2".to_string())),
            ),
        );
    }

    #[test]
    fn or_operator() {
        test_parser(
            SylqParser::parse(Rule::expr, "var1 || var2"),
            expr,
            Expr::Binop(
                Box::new(Expr::Identifier("var1".to_string())),
                Op::Or,
                Box::new(Expr::Identifier("var2".to_string())),
            ),
        );
    }

    #[test]
    fn lt_operator() {
        test_parser(
            SylqParser::parse(Rule::expr, "9 < 10"),
            expr,
            Expr::Binop(
                Box::new(Expr::Integer(9)),
                Op::Lt,
                Box::new(Expr::Integer(10)),
            ),
        )
    }

    #[test]
    fn lte_operator() {
        test_parser(
            SylqParser::parse(Rule::expr, "9 <= 10"),
            expr,
            Expr::Binop(
                Box::new(Expr::Integer(9)),
                Op::Lte,
                Box::new(Expr::Integer(10)),
            ),
        )
    }

    #[test]
    fn is_in_binop() {
        test_parser(
            SylqParser::parse(Rule::expr, "n is { NodeKind } && 1 == 1"),
            expr,
            Expr::Binop(
                Box::new(Expr::Is(
                    Box::new(Expr::Identifier("n".to_string())),
                    Box::new(QueryPattern {
                        node_pattern: NodePatternsWithBinding {
                            binding: None,
                            node_patterns: NonEmpty::new(NodePattern {
                                kind_pattern: KindPattern::KindName("NodeKind".into()),
                                fields: vec![],
                            }),
                        },
                        predicate: None,
                    }),
                )),
                Op::And,
                Box::new(Expr::Binop(
                    Box::new(Expr::Integer(1)),
                    Op::EqEq,
                    Box::new(Expr::Integer(1)),
                )),
            ),
        );
    }

    #[test]
    fn no_braces_is_in_binop() {
        test_parser(
            SylqParser::parse(Rule::expr, "n is NodeKind && 1 == 1"),
            expr,
            Expr::Binop(
                Box::new(Expr::Is(
                    Box::new(Expr::Identifier("n".to_string())),
                    Box::new(QueryPattern {
                        node_pattern: NodePatternsWithBinding {
                            binding: None,
                            node_patterns: NonEmpty::new(NodePattern {
                                kind_pattern: KindPattern::KindName("NodeKind".into()),
                                fields: vec![],
                            }),
                        },
                        predicate: None,
                    }),
                )),
                Op::And,
                Box::new(Expr::Binop(
                    Box::new(Expr::Integer(1)),
                    Op::EqEq,
                    Box::new(Expr::Integer(1)),
                )),
            ),
        );
    }

    #[test]
    fn pattern_identifier() {
        test_parser(
            SylqParser::parse(Rule::node_pattern, "NodeKind"),
            node_pattern,
            NodePatternsWithBinding {
                binding: None,
                node_patterns: NonEmpty::new(NodePattern {
                    kind_pattern: KindPattern::KindName("NodeKind".into()),
                    fields: vec![],
                }),
            },
        )
    }

    #[test]
    fn pattern_or_kind() {
        test_parser(
            SylqParser::parse(Rule::node_pattern, "NodeKind | OtherNodeKind"),
            node_pattern,
            NodePatternsWithBinding {
                binding: None,
                node_patterns: NonEmpty::from((
                    NodePattern {
                        kind_pattern: KindPattern::KindName("NodeKind".into()),
                        fields: vec![],
                    },
                    vec![NodePattern {
                        kind_pattern: KindPattern::KindName("OtherNodeKind".into()),
                        fields: vec![],
                    }],
                )),
            },
        )
    }

    #[test]
    fn node_kind_query() {
        let query = parse_query("match NodeKind").unwrap();
        assert_eq!(
            query,
            QueryPattern {
                node_pattern: NodePatternsWithBinding {
                    binding: None,
                    node_patterns: NonEmpty::new(NodePattern {
                        kind_pattern: KindPattern::KindName("NodeKind".into()),
                        fields: vec![],
                    }),
                },
                predicate: None,
            }
        );
    }

    #[test]
    fn node_list_kind_query() {
        let query = parse_query("match List<NodeKind>").unwrap();
        assert_eq!(
            query,
            QueryPattern {
                node_pattern: NodePatternsWithBinding {
                    binding: None,
                    node_patterns: NonEmpty::new(NodePattern {
                        kind_pattern: KindPattern::KindName("List<NodeKind>".to_string()),
                        fields: vec![],
                    })
                },
                predicate: None,
            }
        )
    }

    #[test]
    fn placeholder_query() {
        assert_eq!(
            parse_query("match _").unwrap(),
            QueryPattern {
                node_pattern: NodePatternsWithBinding {
                    binding: None,
                    node_patterns: NonEmpty::new(NodePattern {
                        kind_pattern: KindPattern::Placeholder,
                        fields: vec![],
                    }),
                },
                predicate: None,
            }
        )
    }

    #[test]
    fn kind_name_with_binding() {
        assert_eq!(
            parse_query("match NodeKind n").unwrap(),
            QueryPattern {
                node_pattern: NodePatternsWithBinding {
                    binding: Some("n".to_string()),
                    node_patterns: NonEmpty::new(NodePattern {
                        kind_pattern: KindPattern::KindName("NodeKind".to_string()),
                        fields: vec![],
                    }),
                },
                predicate: None,
            }
        )
    }

    #[test]
    fn kind_name_with_pre_binding() {
        assert_eq!(
            parse_query("match n@NodeKind").unwrap(),
            QueryPattern {
                node_pattern: NodePatternsWithBinding {
                    binding: Some("n".to_string()),
                    node_patterns: NonEmpty::new(NodePattern {
                        kind_pattern: KindPattern::KindName("NodeKind".to_string()),
                        fields: vec![],
                    }),
                },
                predicate: None,
            }
        )
    }

    #[test]
    fn kind_name_with_field_patterns() {
        assert_eq!(
            parse_query(r##"match NodeKind(field1: "hello", field2: FieldKind)"##).unwrap(),
            QueryPattern {
                node_pattern: NodePatternsWithBinding {
                    binding: None,
                    node_patterns: NonEmpty::new(NodePattern {
                        kind_pattern: KindPattern::KindName("NodeKind".to_string()),
                        fields: vec![
                            NodePatternField {
                                desc: NodePatternFieldDesc::Identifier("field1".to_string()),
                                value: NodePatternFieldValue::Text("hello".to_string()),
                            },
                            NodePatternField {
                                desc: NodePatternFieldDesc::Identifier("field2".to_string()),
                                value: NodePatternFieldValue::Pattern(QueryPattern {
                                    node_pattern: NodePatternsWithBinding {
                                        binding: None,
                                        node_patterns: NonEmpty::new(NodePattern {
                                            kind_pattern: KindPattern::KindName(
                                                "FieldKind".to_string()
                                            ),
                                            fields: vec![],
                                        }),
                                    },
                                    predicate: None,
                                }),
                            },
                        ],
                    }),
                },
                predicate: None,
            }
        )
    }

    #[test]
    fn is_predicate() {
        assert_eq!(
            parse_query("match _ n when n.parent is { ParentKind p when p.text.length == 0 }")
                .unwrap(),
            QueryPattern {
                node_pattern: NodePatternsWithBinding {
                    binding: Some("n".to_string()),
                    node_patterns: NonEmpty::new(NodePattern {
                        kind_pattern: KindPattern::Placeholder,
                        fields: vec![],
                    }),
                },
                predicate: Some(Expr::Is(
                    Box::new(Expr::DotAccess(
                        false,
                        Box::new(Expr::Identifier("n".to_string())),
                        "parent".to_string(),
                    )),
                    Box::new(QueryPattern {
                        node_pattern: NodePatternsWithBinding {
                            binding: Some("p".to_string()),
                            node_patterns: NonEmpty::new(NodePattern {
                                kind_pattern: KindPattern::KindName("ParentKind".to_string()),
                                fields: vec![],
                            }),
                        },
                        predicate: Some(Expr::Binop(
                            Box::new(Expr::DotAccess(
                                false,
                                Box::new(Expr::DotAccess(
                                    false,
                                    Box::new(Expr::Identifier("p".to_string())),
                                    "text".to_string(),
                                )),
                                "length".to_string(),
                            )),
                            Op::EqEq,
                            Box::new(Expr::Integer(0)),
                        )),
                    },),
                )),
            }
        );
    }

    #[test]
    fn with_simple_condition() {
        assert_eq!(
            parse_query("match Identifier i when i.text.length <= 10").unwrap(),
            QueryPattern {
                node_pattern: NodePatternsWithBinding {
                    binding: Some("i".to_string()),
                    node_patterns: NonEmpty::new(NodePattern {
                        kind_pattern: KindPattern::KindName("Identifier".to_string()),
                        fields: vec![],
                    }),
                },
                predicate: Some(Expr::Binop(
                    Box::new(Expr::DotAccess(
                        false,
                        Box::new(Expr::DotAccess(
                            false,
                            Box::new(Expr::Identifier("i".to_string())),
                            "text".to_string(),
                        )),
                        "length".to_string(),
                    )),
                    Op::Lte,
                    Box::new(Expr::Integer(10)),
                )),
            }
        )
    }
}
