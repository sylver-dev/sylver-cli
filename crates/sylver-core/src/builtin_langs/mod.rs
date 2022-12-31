use std::{
    collections::BTreeMap,
    fmt::{Display, Formatter},
    ops::Deref,
};

use anyhow::anyhow;
use non_empty_vec::NonEmpty;
use once_cell::sync::Lazy;
use serde::{Deserialize, Serialize};

use sylver_dsl::meta::*;

use crate::core::spec::{Syntax, SyntaxBuilder};

pub mod parser;

static PYTHON_MAPPING: Lazy<MappingConfig> =
    Lazy::new(|| serde_yaml::from_str(include_str!("../../res/ts_mappings/python.yaml")).unwrap());

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
pub enum BuiltinLang {
    Python,
}

impl Display for BuiltinLang {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let lang_name = match self {
            BuiltinLang::Python => "python",
        };

        lang_name.fmt(f)
    }
}

impl TryFrom<&str> for BuiltinLang {
    type Error = anyhow::Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "python" => Ok(BuiltinLang::Python),
            _ => Err(anyhow!("Unsupported language: {}", value)),
        }
    }
}

pub fn get_builtin_lang(lang: BuiltinLang) -> (&'static MappingConfig, tree_sitter::Language) {
    match lang {
        BuiltinLang::Python => (PYTHON_MAPPING.deref(), sylver_langs::python_language()),
    }
}

pub fn builtin_lang_mappings(lang: BuiltinLang) -> &'static [NodeMapping] {
    match lang {
        BuiltinLang::Python => PYTHON_MAPPING.types.as_slice(),
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct MappingConfig {
    pub types: Vec<NodeMapping>,
    pub aliases: Vec<NodeAlias>,
    pub promotions: Option<Vec<NodePromotion>>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct NodeAlias {
    ts_name: String,
    alias: String,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct NodePromotion {
    parent_kind: String,
    self_ts_kind: String,
    new_kind: String,
    field: Option<String>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct NodeMapping {
    name: String,
    ts_name: Option<String>,
    fields: Vec<NodeMappingField>,
    is_list: bool,
    is_terminal: bool,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
struct NodeMappingField {
    name: String,
    types: Vec<String>,
    list: bool,
    mappings: Option<BTreeMap<String, String>>,
}

impl From<&[NodeMapping]> for Syntax {
    fn from(mappings: &[NodeMapping]) -> Self {
        let decls = mappings.iter().map(|m| {
            if m.is_terminal {
                Decl::Terminal(term_decl_from_mapping(m))
            } else {
                Decl::Node(node_decl_from_mapping(m))
            }
        });

        SyntaxBuilder::new().build(decls).unwrap()
    }
}

fn term_decl_from_mapping(m: &NodeMapping) -> TermDecl {
    TermDecl {
        name: m.name.clone(),
        reg: TermContent::Literal(fancy_regex::Regex::new(&m.name).unwrap()),
        data: None,
    }
}

fn node_decl_from_mapping(m: &NodeMapping) -> NodeDecl {
    NodeDecl {
        name: m.name.clone(),
        parent_type: None,
        fields: m
            .fields
            .iter()
            .map(|f| {
                let field_type = if f.types.len() > 1 {
                    let first = SimpleTypeLit::from_name(f.types[0].clone());

                    let rest = f.types[1..]
                        .iter()
                        .map(|t| SimpleTypeLit::from_name(t.clone()))
                        .collect();

                    TypeLit::Or(OrTypeLit {
                        alts: NonEmpty::from((first, rest)),
                    })
                } else {
                    TypeLit::Simple(SimpleTypeLit::from_name(f.name.clone()))
                };

                let lit = if f.list {
                    TypeLit::list_of(field_type)
                } else {
                    field_type
                };

                (f.name.to_string(), lit)
            })
            .collect(),
    }
}

#[cfg(test)]
mod test {
    use crate::{
        builtin_langs::parser::BuiltinParserRunner, core::source::Source,
        pretty_print::tree::TreePPrint, tree::info::raw::RawTreeInfo,
    };
    use indoc::indoc;

    use super::*;

    #[test]
    fn python_simple() {
        let syntax = PYTHON_MAPPING.types.as_slice().into();
        let runner =
            BuiltinParserRunner::new(sylver_langs::python_language(), &syntax, &PYTHON_MAPPING);
        let source = Source::inline("hello + world".to_string(), "BUFFER".to_string());
        let tree = runner.run(source).tree;
        let pprint = TreePPrint::new(RawTreeInfo::new(&tree, &syntax));

        let expected = indoc!(
            "
            Module {
            . ExpressionStatement {
            . . BinaryOperator {
            . . . ● left: Identifier { hello }
            . . . ● operator: Add { + }
            . . . ● right: Identifier { world }
            . . }
            . }
            }"
        );

        assert_eq!(expected, pprint.render());
    }
}
