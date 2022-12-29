use std::collections::HashMap;

use tree_sitter::Point;

use crate::builtin_langs::NodeMapping;
use crate::core::pos::{InclPosRange, Pos};
use crate::core::source::{Source, SourceTree};
use crate::core::spec::{FieldPos, KindId, Syntax, TagId};
use crate::parsing::parser_runner::ParsingResult;
use crate::parsing::scanner::Token;
use crate::tree::{NodeId, Tree, TreeBuilder};

type NodeWithField = (Option<FieldPos>, NodeId);

pub struct TsTreeConverter<'t> {
    builder: TreeBuilder<'t>,
    syntax: &'t Syntax,
    kind_names: &'t HashMap<u16, String>,
}

impl<'t> TsTreeConverter<'t> {
    pub fn new(syntax: &'t Syntax, kind_names: &'t HashMap<u16, String>) -> Self {
        TsTreeConverter {
            builder: TreeBuilder::new(syntax),
            syntax,
            kind_names,
        }
    }

    pub fn convert(&mut self, root: tree_sitter::Node) -> anyhow::Result<(Tree, Vec<Token>)> {
        let (root_id, _) = self.convert_from(root)?;
        self.builder.set_root(root_id)?;
        Ok(self.build_and_reset_builder())
    }

    fn convert_from(&mut self, node: tree_sitter::Node) -> anyhow::Result<(NodeId, Vec<usize>)> {
        let kind_name = self.kind_names.get(&node.kind_id()).unwrap();
        let kind_id: KindId = self.syntax.existing_kind_id(kind_name);

        let (node_childs, mut node_tokens) = self.convert_childs(kind_id, node)?;

        if node_childs.is_empty() && node_tokens.is_empty() {
            self.add_node_tokens(node, &mut node_tokens);
        }

        Ok((
            self.builder.add_node(kind_id, &node_childs, &node_tokens),
            node_tokens,
        ))
    }

    fn convert_childs(
        &mut self,
        kind_id: KindId,
        node: tree_sitter::Node,
    ) -> anyhow::Result<(Vec<NodeWithField>, Vec<usize>)> {
        let mut childs = vec![];
        let mut tokens_pos = vec![];
        let mut cursor = node.walk();

        for (child_pos, child) in node.children(&mut cursor).enumerate() {
            if child.is_named() {
                let field_name = node.field_name_for_child(child_pos as u32);
                let field_pos = field_name.and_then(|n| self.syntax.field_position(kind_id, n));
                let (child_node, child_tokens) = self.convert_from(child)?;
                childs.push((field_pos, child_node));
                tokens_pos.extend(child_tokens);
            } else {
                self.add_node_tokens(child, &mut tokens_pos);
            }
        }

        Ok((childs, tokens_pos))
    }

    fn add_node_tokens(&mut self, node: tree_sitter::Node, token_pos: &mut Vec<usize>) {
        let tag: TagId = (node.kind_id() as usize).into();
        let token = Token::new(node.range().into(), tag);
        token_pos.push(self.builder.add_token(token))
    }

    fn build_and_reset_builder(&mut self) -> (Tree, Vec<Token>) {
        let builder = std::mem::replace(&mut self.builder, TreeBuilder::new(self.syntax));
        builder.build()
    }
}

impl From<tree_sitter::Range> for InclPosRange {
    fn from(range: tree_sitter::Range) -> Self {
        let start = point_to_pos(range.start_point, range.start_byte);
        let end = point_to_pos(range.end_point, range.end_byte);
        InclPosRange::new(start, end).unwrap()
    }
}

fn point_to_pos(point: Point, byte_pos: usize) -> Pos {
    Pos::new((point.column + 1, point.row + 1), byte_pos)
}

#[derive(Debug, Clone)]
pub struct BuiltinParserRunner<'s> {
    syntax: &'s Syntax,
    language: tree_sitter::Language,
    kind_names: HashMap<u16, String>,
}

impl<'s> BuiltinParserRunner<'s> {
    pub fn new(
        language: tree_sitter::Language,
        syntax: &'s Syntax,
        mappings: &[NodeMapping],
    ) -> BuiltinParserRunner<'s> {
        let ts_name_to_name: HashMap<&str, &str> = mappings
            .iter()
            .map(|m| (m.ts_name.as_str(), m.name.as_str()))
            .collect();

        let kind_names = (0..language.node_kind_count() as u16)
            .filter_map(|n| {
                language
                    .node_kind_for_id(n)
                    .and_then(|k| ts_name_to_name.get(k).map(|name| (n, name.to_string())))
            })
            .collect();

        BuiltinParserRunner {
            syntax,
            language,
            kind_names,
        }
    }

    pub fn run(&self, source: Source) -> ParsingResult {
        let mut ts_parser = tree_sitter::Parser::new();
        ts_parser
            .set_language(self.language)
            .expect("Builtin language should always be valid !");

        let ts_tree = ts_parser.parse(source.src(), None).unwrap();
        let (tree, tokens) = TsTreeConverter::new(self.syntax, &self.kind_names)
            .convert(ts_tree.root_node())
            .unwrap();

        ParsingResult {
            tree: SourceTree::new(source, tokens, tree),
            reports: vec![],
        }
    }
}
