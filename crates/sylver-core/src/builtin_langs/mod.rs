use std::{
    collections::BTreeMap,
    fmt::{Display, Formatter},
    ops::Deref,
};

use anyhow::anyhow;
use once_cell::sync::Lazy;
use serde::{Deserialize, Serialize};

use sylver_dsl::meta::*;

use crate::core::spec::{Syntax, SyntaxBuilder};

pub mod parser;

static PYTHON_MAPPING: Lazy<MappingConfig> =
    Lazy::new(|| serde_yaml::from_str(include_str!("../../res/ts_mappings/python.yaml")).unwrap());

static JAVASCRIPT_MAPPING: Lazy<MappingConfig> = Lazy::new(|| {
    serde_yaml::from_str(include_str!("../../res/ts_mappings/javascript.yaml")).unwrap()
});

static YAML_MAPPING: Lazy<MappingConfig> =
    Lazy::new(|| serde_yaml::from_str(include_str!("../../res/ts_mappings/yaml.yaml")).unwrap());

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(tag = "name", rename_all = "snake_case")]
pub enum BuiltinLang {
    Python,
    Javascript,
    Yaml,
}

impl Display for BuiltinLang {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let lang_name = match self {
            BuiltinLang::Python => "python",
            BuiltinLang::Javascript => "javascript",
            BuiltinLang::Yaml => "yaml",
        };

        lang_name.fmt(f)
    }
}

impl TryFrom<&str> for BuiltinLang {
    type Error = anyhow::Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "python" => Ok(BuiltinLang::Python),
            "javascript" => Ok(BuiltinLang::Javascript),
            "yaml" => Ok(BuiltinLang::Yaml),
            _ => Err(anyhow!("Unsupported language: {}", value)),
        }
    }
}

pub fn get_detection_script(lang: BuiltinLang) -> &'static str {
    match lang {
        BuiltinLang::Python => include_str!("../../res/detection_scripts/python.py"),
        BuiltinLang::Javascript => include_str!("../../res/detection_scripts/javascript.py"),
        BuiltinLang::Yaml => include_str!("../../res/detection_scripts/yaml.py"),
    }
}

pub fn get_builtin_langs() -> Vec<BuiltinLang> {
    vec![
        BuiltinLang::Python,
        BuiltinLang::Javascript,
        BuiltinLang::Yaml,
    ]
}

pub fn get_builtin_lang(lang: BuiltinLang) -> (&'static MappingConfig, tree_sitter::Language) {
    match lang {
        BuiltinLang::Python => (PYTHON_MAPPING.deref(), sylver_langs::python_language()),
        BuiltinLang::Javascript => (
            JAVASCRIPT_MAPPING.deref(),
            sylver_langs::javascript_language(),
        ),
        BuiltinLang::Yaml => (YAML_MAPPING.deref(), sylver_langs::yaml_language()),
    }
}

pub fn builtin_lang_mappings(lang: BuiltinLang) -> &'static [NodeMapping] {
    match lang {
        BuiltinLang::Python => PYTHON_MAPPING.types.as_slice(),
        BuiltinLang::Javascript => JAVASCRIPT_MAPPING.types.as_slice(),
        BuiltinLang::Yaml => YAML_MAPPING.types.as_slice(),
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct MappingConfig {
    pub types: Vec<NodeMapping>,
    pub aliases: Vec<NodeAlias>,
    pub fields: Vec<FieldSettings>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct FieldSettings {
    pub parent_kind: String,
    pub ts_kind: String,
    pub new_kind: String,
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
    inherits: Option<String>,
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
        parent_type: m.inherits.clone(),
        fields: m
            .fields
            .iter()
            .map(|f| {
                let field_type = TypeLit::from_simple_types(
                    f.types.iter().map(|n| SimpleTypeLit::from_name(n.clone())),
                )
                .expect("node field missing associated types");

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
    use tree_sitter::Language;

    use super::*;

    #[test]
    fn python_error() {
        let expected = indoc!(
            "
            Module {
            . FunctionDefinition {
            . . ● name: Error {
            . . . Error { $ }
            . . }
            . . ● parameters: Identifier { _hello }
            . . Parameters { () }
            . . Block {  }
            . }
            }"
        );

        test_builtin_parser(
            sylver_langs::python_language(),
            PYTHON_MAPPING.types.as_slice().into(),
            &PYTHON_MAPPING,
            "def $_hello():",
            expected,
        );
    }

    #[test]
    fn python_simple() {
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

        test_builtin_parser(
            sylver_langs::python_language(),
            PYTHON_MAPPING.types.as_slice().into(),
            &PYTHON_MAPPING,
            "hello + world",
            expected,
        );
    }

    #[test]
    fn javascript_simple() {
        let expected = indoc!(
            "
        Program {
        . ExpressionStatement {
        . . CallExpression {
        . . . ● function: MemberExpression {
        . . . . ● object: Identifier { console }
        . . . . ● property: Identifier { log }
        . . . }
        . . . ● arguments: Arguments {
        . . . . BinaryExpression {
        . . . . . ● left: Identifier { hello }
        . . . . . ● operator: Add { + }
        . . . . . ● right: Identifier { world }
        . . . . }
        . . . }
        . . }
        . }
        }"
        );

        test_builtin_parser(
            sylver_langs::javascript_language(),
            JAVASCRIPT_MAPPING.types.as_slice().into(),
            &JAVASCRIPT_MAPPING,
            "console.log(hello + world)",
            expected,
        );
    }

    #[test]
    fn yaml_simple() {
        let expected = indoc!(
            "
        Stream {
        . Document {
        . . BlockNode {
        . . . BlockMapping {
        . . . . BlockMappingPair {
        . . . . . ● key: FlowNode {
        . . . . . . PlainScalar {
        . . . . . . . StringScalar { hello }
        . . . . . . }
        . . . . . }
        . . . . . FlowNode {
        . . . . . . PlainScalar {
        . . . . . . . StringScalar { world }
        . . . . . . }
        . . . . . }
        . . . . }
        . . . }
        . . }
        . }
        }"
        );

        test_builtin_parser(
            sylver_langs::yaml_language(),
            YAML_MAPPING.types.as_slice().into(),
            &YAML_MAPPING,
            "hello: world",
            expected,
        );
    }

    fn test_builtin_parser(
        language: Language,
        syntax: Syntax,
        mapping_config: &MappingConfig,
        src: &str,
        expected: &str,
    ) {
        let runner = BuiltinParserRunner::new(language, &syntax, mapping_config);
        let source = Source::inline(src.to_string(), "BUFFER".to_string());
        let tree = runner.run(source).tree;
        let pprint = TreePPrint::new(RawTreeInfo::new(&tree, &syntax));

        assert_eq!(expected, pprint.render());
    }
}
