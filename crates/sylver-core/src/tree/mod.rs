use std::cmp::{max, min};
use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
    ops::Index,
};

use anyhow::{anyhow, Result};
use id_vec::{Id, IdVec};

use crate::util::iter::first_and_last;
use crate::{
    core::spec::{FieldPos, KindId, Syntax},
    id_type,
    parsing::{scanner::Token, sppf::Span},
};

pub mod info;

id_type!(NodeId: Node);

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Node {
    pub kind: KindId,
    pub span: Span,
    pub parent: Option<NodeId>,
    /// Vector storing the position of the (possibly null) node matching field
    /// with pos `P` at the `P`th position.
    pub named_childs: Vec<Option<usize>>,
    pub childs: Vec<NodeId>,
}

impl Node {
    /// If the nth child corresponds to a name field, return it's field position, otherwise return
    /// `None`.
    pub fn nth_child_field_pos(&self, n: usize) -> Option<FieldPos> {
        self.named_childs
            .iter()
            .position(|&opt_pos| matches!(opt_pos, Some(pos) if pos == n))
            .map(Into::into)
    }
}

#[derive(Debug, Clone, Eq)]
pub struct Tree {
    root: NodeId,
    nodes: IdVec<Node>,
}

impl Tree {
    /// Create a new, empty tree.
    pub fn new() -> Tree {
        Tree {
            root: NodeId::from(0),
            nodes: IdVec::new(),
        }
    }

    /// Return the root of the `Tree`
    pub fn root(&self) -> NodeId {
        self.root
    }

    /// Set the root id.
    pub fn set_root(&mut self, root: NodeId) -> Result<()> {
        if self.nodes.get(root.into()).is_none() {
            return Err(anyhow!("Cannot set non-existing node as root: {:?}", root));
        }

        self.root = root;

        Ok(())
    }

    fn add_node(&mut self, node: Node) -> NodeId {
        self.nodes.insert(node).into()
    }

    /// Return the node with the given id, if it exists.
    pub fn get_node(&self, id: NodeId) -> Option<&Node> {
        self.nodes.get(id.into())
    }

    pub fn get_existing_node(&self, id: NodeId) -> &Node {
        self.nodes
            .get(id.into())
            .unwrap_or_else(|| panic!("Non existing node id: {id:?}"))
    }

    /// Return an iterator over the node's ids.
    pub fn bottom_up_node_ids(&'_ self) -> impl '_ + Iterator<Item = NodeId> {
        self.nodes.ids().map(Into::into)
    }

    pub fn top_down_node_ids(&'_ self) -> impl '_ + Iterator<Item = NodeId> {
        self.nodes.ids().rev().map(Into::into)
    }
}

impl Default for Tree {
    fn default() -> Self {
        Tree::new()
    }
}

impl Index<NodeId> for Tree {
    type Output = Node;

    fn index(&self, index: NodeId) -> &Node {
        self.get_node(index).unwrap()
    }
}

impl PartialEq for Tree {
    fn eq(&self, other: &Self) -> bool {
        self.root.eq(&other.root) && self.nodes.eq(&other.nodes)
    }
}

impl Hash for Tree {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.root.hash(state);

        for n in self.nodes.iter() {
            n.hash(state);
        }
    }
}

#[derive(Debug)]
pub struct TreeBuilder<'e> {
    syntax: &'e Syntax,
    tree: Tree,
    tokens: Vec<Token>,
}

impl<'e> TreeBuilder<'e> {
    /// Create a new editor.
    pub fn new(syntax: &'e Syntax) -> Self {
        TreeBuilder {
            syntax,
            tree: Tree::new(),
            tokens: Vec::new(),
        }
    }

    /// Return the built tree and tokens vector.
    pub fn build(self) -> (Tree, Vec<Token>) {
        (self.tree, self.tokens)
    }

    /// Set the root of the tree.
    pub fn set_root(&mut self, root: NodeId) -> Result<()> {
        self.tree.set_root(root)
    }

    /// Set the parent of a given node.
    pub fn set_parent(&mut self, parent: NodeId, node: NodeId) {
        self.tree.nodes[node.into()].parent = Some(parent);
    }

    /// Add a `Token` to the tokens list, and return it's position.
    pub fn add_token(&mut self, token: Token) -> usize {
        let pos = self.tokens.len();
        self.tokens.push(token);
        pos
    }

    /// Add a new node to the tree.
    /// # panics
    /// If a named node is missing from the childs list, or one of the nodes child wasn't previously
    /// added to the tree.
    pub fn add_node(
        &mut self,
        kind: KindId,
        childs: &[(Option<FieldPos>, NodeId)],
        tokens: &[usize],
    ) -> NodeId {
        let node_decl = &self.syntax[kind];

        self.span_from_childs(childs.iter().map(|(_, c)| *c));
        let span = self.span_from_tokens_and_childs(tokens, childs.iter().map(|(_, c)| *c));

        let named_childs = node_decl
            .fields
            .keys()
            .map(|f| {
                let field_pos = self.syntax.field_position(kind, f).unwrap();
                childs.iter().position(|(pos, _)| *pos == Some(field_pos))
            })
            .collect();

        let new_node = Node {
            kind,
            span,
            parent: None,
            named_childs,
            childs: childs.iter().map(|(_, id)| *id).collect(),
        };

        self.add_node_and_set_parent(new_node)
    }

    /// Add a named list node the the tree.
    /// The field will be used to determine the kind of the elements stored in
    /// the list.
    pub fn add_list_node(&mut self, childs: &[NodeId], tokens: &[usize]) -> NodeId {
        self.add_node_and_set_parent(Node {
            span: self.span_from_tokens_and_childs(tokens, childs.iter().copied()),
            kind: self.syntax.list_kind(),
            parent: None,
            named_childs: vec![],
            childs: childs.into(),
        })
    }

    fn add_node_and_set_parent(&mut self, node: Node) -> NodeId {
        let child_ids = node.childs.clone();
        let new_id = self.tree.add_node(node);

        for child_id in child_ids {
            self.set_parent(new_id, child_id);
        }

        new_id
    }

    fn span_from_tokens_and_childs(
        &self,
        tokens: &[usize],
        childs: impl IntoIterator<Item = NodeId>,
    ) -> Span {
        match (self.span_from_tokens(tokens), self.span_from_childs(childs)) {
            (None, Some(cs)) => cs,
            (Some(ts), None) => ts,
            (Some(ts), Some(cs)) => {
                let start = min(ts.start, cs.start);
                let end_pos = max(ts.most_advanced_pos(), cs.most_advanced_pos());
                Span {
                    start,
                    length: (end_pos - start),
                }
            }
            _ => Span::new(self.tokens.len(), 0),
        }
    }

    fn span_from_tokens(&self, tokens: &[usize]) -> Option<Span> {
        first_and_last(tokens).map(|(first, last)| Span::new(*first, last - first + 1))
    }

    fn span_from_childs(&self, childs: impl IntoIterator<Item = NodeId>) -> Option<Span> {
        first_and_last(childs).map(|(first_id, last_id)| {
            let first = &self.tree[first_id].span;
            let last = &self.tree[last_id].span;
            join_spans(*first, *last)
        })
    }
}

fn join_spans(first: Span, last: Span) -> Span {
    let start = first.start;
    let length = (last.start - start) + (last.length);
    Span { start, length }
}
