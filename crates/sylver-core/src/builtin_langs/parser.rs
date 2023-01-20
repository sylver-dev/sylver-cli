use std::collections::HashMap;

use tree_sitter::Point;

use crate::{
    builtin_langs::MappingConfig,
    core::{
        pos::{InclPosRange, Pos},
        source::{Source, SourceTree},
        spec::{FieldPos, KindId, Syntax, TagId},
    },
    parsing::{parser_runner::ParsingResult, scanner::Token},
    tree::{NodeId, Tree, TreeBuilder},
};

type NodeWithField = (Option<FieldPos>, NodeId);

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TsMappings {
    /// Maps a tree-sitter kind to the corresponding sylver kind id.
    pub kinds: HashMap<u16, KindId>,
    /// For every node matching a (parent sylver kind, tree-sitter kind) pair, create a wrapping
    /// node with the given sylver kind.
    pub field_kinds: HashMap<(KindId, u16), KindId>,
}

pub struct TsTreeConverter<'t> {
    builder: TreeBuilder<'t>,
    syntax: &'t Syntax,
    mappings: &'t TsMappings,
}

impl<'t> TsTreeConverter<'t> {
    pub fn new(syntax: &'t Syntax, mappings: &'t TsMappings) -> Self {
        TsTreeConverter {
            builder: TreeBuilder::new(syntax),
            syntax,
            mappings,
        }
    }

    pub fn convert(&mut self, root: tree_sitter::Node) -> anyhow::Result<(Tree, Vec<Token>)> {
        let (root_id, _) = self.convert_from(root)?;
        self.builder.set_root(root_id)?;
        Ok(self.build_and_reset_builder())
    }

    fn convert_from(&mut self, node: tree_sitter::Node) -> anyhow::Result<(NodeId, Vec<usize>)> {
        let kind_id = *self.mappings.kinds.get(&node.kind_id()).unwrap();

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
            let field_name = node.field_name_for_child(child_pos as u32);

            let field_pos = field_name.and_then(|n| self.syntax.field_position(kind_id, n));

            if child.is_named() {
                let (child_node, child_tokens) = self.convert_from(child)?;
                childs.push((field_pos, child_node));
                tokens_pos.extend(child_tokens);
            } else {
                let mut field_tokens = vec![];
                self.add_node_tokens(child, &mut field_tokens);

                if let Some(&field_kind) =
                    self.mappings.field_kinds.get(&(kind_id, child.kind_id()))
                {
                    let new_node = self.builder.add_node(field_kind, &[], &field_tokens);
                    childs.push((field_pos, new_node));
                }

                tokens_pos.extend(field_tokens);
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
    Pos::new((point.row + 1, point.column + 1), byte_pos)
}

#[derive(Debug, Clone)]
pub struct BuiltinParserRunner<'s> {
    syntax: &'s Syntax,
    language: tree_sitter::Language,
    ts_mappings: TsMappings,
}

impl<'s> BuiltinParserRunner<'s> {
    pub fn new(
        language: tree_sitter::Language,
        syntax: &'s Syntax,
        mapping_config: &MappingConfig,
    ) -> BuiltinParserRunner<'s> {
        let ts_mappings = Self::build_ts_mappings(&language, syntax, mapping_config);

        BuiltinParserRunner {
            syntax,
            language,
            ts_mappings,
        }
    }

    fn build_ts_mappings(
        language: &tree_sitter::Language,
        syntax: &Syntax,
        mapping_config: &MappingConfig,
    ) -> TsMappings {
        let ts_name_to_name = Self::build_kind_mapping(mapping_config);

        let kind_names = (0..language.node_kind_count() as u16)
            .filter_map(|n| {
                language.node_kind_for_id(n).and_then(|k| {
                    ts_name_to_name
                        .get(k)
                        .map(|name| (n, syntax.existing_kind_id(name)))
                })
            })
            .collect();

        let field_kind = mapping_config
            .fields
            .iter()
            .map(|field| {
                let parent_kind_id = syntax.existing_kind_id(&field.parent_kind);
                let ts_kind_id = language.id_for_node_kind(&field.ts_kind, false);
                let new_kind_id = syntax.existing_kind_id(&field.new_kind);
                ((parent_kind_id, ts_kind_id), new_kind_id)
            })
            .collect();

        TsMappings {
            kinds: kind_names,
            field_kinds: field_kind,
        }
    }

    fn build_kind_mapping(mapping_config: &MappingConfig) -> HashMap<&str, &str> {
        let mut ts_name_to_name: HashMap<&str, &str> = mapping_config
            .types
            .iter()
            .filter_map(|m| m.ts_name.as_ref().map(|n| (n.as_str(), m.name.as_str())))
            .collect();

        for alias in &mapping_config.aliases {
            ts_name_to_name.insert(
                &alias.alias,
                ts_name_to_name.get(alias.ts_name.as_str()).unwrap(),
            );
        }

        ts_name_to_name
    }

    pub fn run(&self, source: Source) -> ParsingResult {
        let mut ts_parser = tree_sitter::Parser::new();
        ts_parser
            .set_language(self.language)
            .expect("Builtin language should always be valid !");

        let ts_tree = ts_parser.parse(source.src(), None).unwrap();
        let (tree, tokens) = TsTreeConverter::new(self.syntax, &self.ts_mappings)
            .convert(ts_tree.root_node())
            .unwrap();

        ParsingResult {
            tree: SourceTree::new(source, tokens, tree),
            reports: vec![],
        }
    }
}
