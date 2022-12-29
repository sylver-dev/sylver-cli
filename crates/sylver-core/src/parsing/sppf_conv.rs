use anyhow::{anyhow, Result};

use crate::{
    core::spec::{FieldPos, Syntax, BUILTIN_LIST_KIND},
    parsing::scanner::Token,
    parsing::sppf::{PackedParseForest, TreeNodeData, TreeNodeId},
    tree::{NodeId, Tree, TreeBuilder},
};

#[derive(Debug)]
pub struct SppfConverter<'t> {
    sppf: &'t PackedParseForest,
    editor: TreeBuilder<'t>,
}

impl<'t> SppfConverter<'t> {
    /// Create a new converter for the given parse forest.
    fn new(sppf: &'t PackedParseForest, editor: TreeBuilder<'t>) -> Self {
        SppfConverter { sppf, editor }
    }

    pub fn convert(mut self) -> Result<(Tree, Vec<Token>)> {
        match self.sppf.root {
            Some(root) => {
                let id = self.convert_from(root)?;
                self.editor.set_root(id)?;

                Ok(self.editor.build())
            }
            None => Ok((Tree::new(), Vec::new())),
        }
    }

    fn convert_from(&mut self, node_id: TreeNodeId) -> Result<NodeId> {
        let node = &self.sppf[node_id];

        match node.data() {
            TreeNodeData::NonTerminal(_, childs) => {
                if let Some(c) = childs.iter().next() {
                    self.convert_from(*c)
                } else {
                    Err(anyhow!("Cannot convert from an empty non-terminal"))
                }
            }
            TreeNodeData::Constructed(kind, child) => {
                let converted = if kind.index() == BUILTIN_LIST_KIND {
                    let mut list_childs = vec![];
                    let mut tokens = vec![];
                    if let Some(packed) = child {
                        self.flatten_list_childs(*packed, &mut list_childs, &mut tokens)?;
                    }

                    self.editor.add_list_node(&list_childs, &tokens)
                } else {
                    let mut childs = Vec::new();
                    let mut tokens = Vec::new();
                    if let Some(c) = child {
                        self.convert_node_child(None, *c, &mut childs, &mut tokens)?;
                    }

                    self.editor.add_node(*kind, &childs, &tokens)
                };

                Ok(converted)
            }
            TreeNodeData::Named(_, n) => self.convert_from(*n),
            data => Err(anyhow!("Invalid SPPF root data: {data:?}")),
        }
    }

    fn convert_node_child(
        &mut self,
        pos: Option<FieldPos>,
        child: TreeNodeId,
        result: &mut Vec<(Option<FieldPos>, NodeId)>,
        tokens_pos: &mut Vec<usize>,
    ) -> Result<()> {
        let node = &self.sppf[child];
        match node.data {
            TreeNodeData::Constructed(kind, child_node) => {
                if kind == BUILTIN_LIST_KIND.into() {
                    let mut list_childs = vec![];
                    let mut list_tokens = vec![];
                    if let Some(packed) = child_node {
                        self.flatten_list_childs(packed, &mut list_childs, &mut list_tokens)?;
                    }

                    let list_node = self.editor.add_list_node(&list_childs, &list_tokens);

                    tokens_pos.extend(list_tokens);
                    result.push((pos, list_node));
                } else {
                    result.push((pos, self.convert_from(child)?));
                }
            }
            TreeNodeData::NonTerminal(_, _) => {
                result.push((pos, self.convert_from(child)?));
            }
            TreeNodeData::Intermediate(packed) => {
                self.convert_node_child(None, packed, result, tokens_pos)?
            }
            TreeNodeData::Packed(l, r) => {
                self.convert_node_child(None, l, result, tokens_pos)?;
                if let Some(r_id) = r {
                    self.convert_node_child(None, r_id, result, tokens_pos)?;
                }
            }
            TreeNodeData::Named(p, c) => self.convert_node_child(Some(p), c, result, tokens_pos)?,
            TreeNodeData::Leaf(t) => {
                tokens_pos.push(self.editor.add_token(t));
            }
            TreeNodeData::Empty => {}
        }

        Ok(())
    }

    fn flatten_list_childs(
        &mut self,
        node_id: TreeNodeId,
        result: &mut Vec<NodeId>,
        tokens_pos: &mut Vec<usize>,
    ) -> Result<()> {
        let node = &self.sppf[node_id];

        match &node.data() {
            TreeNodeData::Leaf(token) => {
                tokens_pos.push(self.editor.add_token(*token));
            }
            TreeNodeData::NonTerminal(_, alts) => {
                self.flatten_list_childs(*alts.iter().next().unwrap(), result, tokens_pos)?;
            }
            TreeNodeData::Constructed(kind, child) => {
                if kind.index() == BUILTIN_LIST_KIND && child.is_some() {
                    self.flatten_list_childs(child.unwrap(), result, tokens_pos)?;
                } else {
                    result.push(self.convert_from(node_id)?)
                }
            }
            TreeNodeData::Named(_, _) => result.push(self.convert_from(node_id)?),
            TreeNodeData::Intermediate(packed) => {
                self.flatten_list_childs(*packed, result, tokens_pos)?
            }
            TreeNodeData::Packed(l, r) => {
                self.flatten_list_childs(*l, result, tokens_pos)?;

                if let Some(r_id) = r {
                    self.flatten_list_childs(*r_id, result, tokens_pos)?;
                }
            }
            TreeNodeData::Empty => {}
        }

        Ok(())
    }
}

pub fn sppf_to_tree(syntax: &Syntax, sppf: &PackedParseForest) -> Result<(Tree, Vec<Token>)> {
    SppfConverter::new(sppf, TreeBuilder::new(syntax)).convert()
}
