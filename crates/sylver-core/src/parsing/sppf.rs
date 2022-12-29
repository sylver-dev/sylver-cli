use std::{
    cmp::Ordering,
    ops::{Index, IndexMut},
};

use id_vec::{Id, IdVec};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::core::pos::InclPosRange;
use crate::parsing::scanner::Token;
use crate::{
    core::spec::{FieldPos, KindId, RuleId, BUILTIN_LIST_KIND, COMMENT_NODE_KIND},
    id_type,
};

pub type TokenPos = usize;

#[derive(Debug, Eq, PartialEq, Copy, Clone, Hash)]
pub struct Span {
    pub start: TokenPos,
    // position of the first token of the node
    pub length: usize, // span length (in tokens)
}

impl Span {
    /// Create a position span of the given length at the given start position.
    pub const fn new(start: TokenPos, length: usize) -> Span {
        Span { start, length }
    }

    /// A span can have a length of 0 (in case of a node without children). In this case the most
    /// advanced position is the start position. Otherwise it is the end position.
    pub fn most_advanced_pos(&self) -> TokenPos {
        self.start + self.length
    }

    pub fn end(&self) -> Option<TokenPos> {
        if self.length > 0 {
            Some(self.start + self.length - 1)
        } else {
            None
        }
    }

    /// Return the span's length.
    pub fn length(&self) -> usize {
        self.length
    }
}

impl From<InclPosRange> for Span {
    fn from(range: InclPosRange) -> Self {
        let start = range.start().txt_pos;
        let end = range.end().txt_pos;
        Span::new(start, end - start)
    }
}

id_type!(TreeNodeId: TreeNode);

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TreeNode {
    pub data: TreeNodeData,
    pub span: Span,
}

impl TreeNode {
    pub fn data(&self) -> &TreeNodeData {
        &self.data
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn is_leaf(&self) -> bool {
        matches!(self.data, TreeNodeData::Leaf(_))
    }

    /// Create a new leaf tree node.
    pub fn leaf(token: Token, span: Span) -> TreeNode {
        TreeNode::with_data(TreeNodeData::Leaf(token), span)
    }

    /// Create an intermediate tree node.
    pub fn intermediate(packed_node: TreeNodeId, span: Span) -> TreeNode {
        TreeNode::with_data(TreeNodeData::Intermediate(packed_node), span)
    }

    /// Create a packed node
    pub fn packed(left: TreeNodeId, right: Option<TreeNodeId>, span: Span) -> TreeNode {
        TreeNode::with_data(TreeNodeData::Packed(left, right), span)
    }

    /// Create a non-terminal node
    pub fn non_terminal(rule: RuleId, childs: FxHashSet<TreeNodeId>, span: Span) -> TreeNode {
        TreeNode::with_data(TreeNodeData::NonTerminal(rule, childs), span)
    }

    /// Create a node built from a contructor.
    pub fn constructed(kind: KindId, child: Option<TreeNodeId>, span: Span) -> TreeNode {
        TreeNode::with_data(TreeNodeData::Constructed(kind, child), span)
    }

    /// Create a new empty node.
    pub fn empty(span: Span) -> TreeNode {
        TreeNode::with_data(TreeNodeData::Empty, span)
    }

    /// Create a new named node.
    pub fn named(field: FieldPos, child: TreeNodeId, span: Span) -> TreeNode {
        TreeNode::with_data(TreeNodeData::Named(field, child), span)
    }

    fn with_data(data: TreeNodeData, span: Span) -> TreeNode {
        TreeNode { data, span }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TreeNodeData {
    Leaf(Token),
    NonTerminal(RuleId, FxHashSet<TreeNodeId>),
    Constructed(KindId, Option<TreeNodeId>),
    Intermediate(TreeNodeId),
    Packed(TreeNodeId, Option<TreeNodeId>),
    Named(FieldPos, TreeNodeId),
    Empty,
}

impl TreeNodeData {
    pub fn is_ignored_node(&self) -> bool {
        matches!(self, TreeNodeData::Constructed(kind, _) if
            kind.index() == BUILTIN_LIST_KIND || kind.index() == COMMENT_NODE_KIND)
    }
}

#[derive(Debug, Clone)]
pub struct PackedParseForest {
    /// Tree nodes
    nodes: IdVec<TreeNode>,
    /// List of tree nodes with the given span, for quick retrieval of existing nodes.
    nodes_by_span: FxHashMap<Span, Vec<TreeNodeId>>,
    /// Latest non terminal node to be added to the tree.
    pub root: Option<TreeNodeId>,
}

impl PackedParseForest {
    /// Create a new, empty packed parse forest.
    pub fn new() -> PackedParseForest {
        PackedParseForest {
            nodes: IdVec::new(),
            nodes_by_span: FxHashMap::default(),
            root: None,
        }
    }

    /// Return the childs of the given node.
    pub fn childs(&self, node: TreeNodeId) -> Vec<TreeNodeId> {
        match &self[node].data {
            TreeNodeData::NonTerminal(_, childs) => childs.iter().copied().collect(),
            TreeNodeData::Packed(left, right) => {
                std::iter::once(left).chain(right.iter()).copied().collect()
            }
            TreeNodeData::Intermediate(child) => vec![*child],
            TreeNodeData::Constructed(_, child) => child.iter().copied().collect(),
            TreeNodeData::Named(_, child) => vec![*child],
            TreeNodeData::Leaf(_) | TreeNodeData::Empty => vec![],
        }
    }

    /// Return an iterator over the sppf's nodes.
    pub fn nodes(&self) -> impl Iterator<Item = &TreeNode> {
        self.nodes.iter().map(|(_, node)| node)
    }

    /// Return whether the parse forest is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Number of nodes in the tree.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Get a reference to the node at `index`.
    pub fn get(&self, index: TreeNodeId) -> &TreeNode {
        &self[index]
    }

    /// Return the node data assicoated with the given node.
    pub fn get_data(&self, index: TreeNodeId) -> &TreeNodeData {
        &self[index].data
    }

    /// Get a mutable reference to the node at `index`.
    pub fn mut_get(&mut self, index: TreeNodeId) -> &mut TreeNode {
        &mut self[index]
    }

    /// Return the most advanced position covered by this tree's span.
    pub fn end_pos(&self) -> Option<TokenPos> {
        self.root.and_then(|id| self.nodes[id.into()].span.end())
    }

    pub fn packed_childs(&self, index: TreeNodeId) -> Option<(TreeNodeId, Option<TreeNodeId>)> {
        match self.get_data(index) {
            TreeNodeData::Packed(left, right) => Some((*left, *right)),
            TreeNodeData::Intermediate(child) => self.packed_childs(*child), // intermediate nodes have packed childs
            _ => None,
        }
    }

    /// Find or create an empty node.
    pub fn empty(&mut self, current_pos: TokenPos) -> TreeNodeId {
        let span = Span::new(current_pos, 0);

        self.find_matching(span, |data| matches!(data, TreeNodeData::Empty))
            .unwrap_or_else(|| self.add_node(TreeNode::empty(span)))
    }

    /// Find or create a new constructed node with the given kind and child node.
    pub fn constructed(
        &mut self,
        current_pos: TokenPos,
        kind: KindId,
        child: Option<TreeNodeId>,
    ) -> TreeNodeId {
        let span = child
            .map(|c| self[c].span)
            .unwrap_or_else(|| Span::new(current_pos, 0));
        let new_node = TreeNode::constructed(kind, child, span);

        self.find_matching(span, |data| data == &new_node.data)
            .unwrap_or_else(|| self.add_node(new_node))
    }

    /// Find or create a non terminal with the given span and slot id. Then add left and rights as
    /// it's (packed) children if necessary.
    pub fn non_terminal(&mut self, rule: RuleId, child: TreeNodeId) -> TreeNodeId {
        let span = self.get(child).span;

        let existing = self.find_matching(
            span,
            |data| matches!(data, TreeNodeData::NonTerminal(s, _) if *s == rule),
        );

        let id = match existing {
            Some(non_terminal_id) => {
                let childs = non_terminal_mut_childs(self.mut_get(non_terminal_id));
                childs.insert(child);
                non_terminal_id
            }
            None => self.create_new_non_terminal(rule, child, span),
        };

        match self.root {
            None => {
                self.root = Some(id);
            }
            Some(root) => {
                if self.get(root).span.length() <= self.get(id).span.length() {
                    self.root = Some(id)
                }
            }
        }

        id
    }

    fn create_new_non_terminal(
        &mut self,
        slot: RuleId,
        child: TreeNodeId,
        span: Span,
    ) -> TreeNodeId {
        self.add_node(TreeNode::non_terminal(
            slot,
            FxHashSet::from_iter([child]),
            span,
        ))
    }

    /// Search an existing intermediate node with the given terminal nodes as children (through a packed node),
    /// and create it if it doesnt exist.
    pub fn intermediate(&mut self, left: TreeNodeId, right: TreeNodeId) -> Option<TreeNodeId> {
        let span = self.span_for_nodes(left, Some(right));

        let existing = self.find_matching(span, |data| {
            matches!(
                data,
                TreeNodeData::Intermediate(packed_id)
                    if self.is_packed_with_childs(*packed_id, left, Some(right))
            )
        });

        existing.or_else(|| {
            let left_span = self[left].span;
            let right_span = self[right].span;

            if right_span.start == (left_span.start + left_span.length) {
                let packed = self.add_node(TreeNode::packed(left, Some(right), span));
                Some(self.add_node(TreeNode::intermediate(packed, span)))
            } else {
                None
            }
        })
    }

    fn is_packed_with_childs(
        &self,
        node_id: TreeNodeId,
        left: TreeNodeId,
        right: Option<TreeNodeId>,
    ) -> bool {
        let node = &self.nodes[node_id.into()];
        matches!(node.data, TreeNodeData::Packed(l, r) if l == left && r == right)
    }

    fn span_for_nodes(&self, left: TreeNodeId, right: Option<TreeNodeId>) -> Span {
        let first_node = &self.nodes[left.into()];
        let last_node = right.map(|id| &self.nodes[id.into()]).unwrap_or(first_node);

        Span {
            start: first_node.span.start,
            length: last_node.span.most_advanced_pos() - first_node.span.start,
        }
    }

    /// Search an existing terminal node with the given tag and range, and create it if it doesn't exist.
    pub fn terminal(&mut self, token: Token) -> TreeNodeId {
        let node = TreeNode::leaf(token, token.pos.into());
        self.find_existing(&node)
            .unwrap_or_else(|| self.add_node(node))
    }

    /// Search an existing named node with the given child and create it if it doesn't exist.
    pub fn named(&mut self, field: FieldPos, child: TreeNodeId) -> TreeNodeId {
        let node = TreeNode::named(field, child, self[child].span);
        self.find_existing(&node)
            .unwrap_or_else(|| self.add_node(node))
    }

    fn add_node(&mut self, node: TreeNode) -> TreeNodeId {
        let span = node.span;
        let id = self.nodes.insert(node).into();
        self.nodes_by_span.entry(span).or_default().push(id);
        id
    }

    fn find_existing(&self, node: &TreeNode) -> Option<TreeNodeId> {
        self.find_matching(node.span, |data| data == &node.data)
    }

    fn find_matching(
        &self,
        span: Span,
        predicate: impl Fn(&TreeNodeData) -> bool,
    ) -> Option<TreeNodeId> {
        self.nodes_by_span
            .get(&span)
            .and_then(|ids| {
                ids.iter()
                    .find(|&&id| predicate(&self.nodes[id.into()].data))
            })
            .copied()
    }
}

impl Default for PackedParseForest {
    fn default() -> Self {
        PackedParseForest::new()
    }
}

impl Index<TreeNodeId> for PackedParseForest {
    type Output = TreeNode;

    fn index(&self, index: TreeNodeId) -> &Self::Output {
        &self.nodes[index.into()]
    }
}

impl IndexMut<TreeNodeId> for PackedParseForest {
    fn index_mut(&mut self, index: TreeNodeId) -> &mut Self::Output {
        &mut self.nodes[index.into()]
    }
}

fn non_terminal_mut_childs(node: &mut TreeNode) -> &mut FxHashSet<TreeNodeId> {
    match node {
        TreeNode {
            data: TreeNodeData::NonTerminal(_, ref mut childs),
            ..
        } => childs,
        _ => panic!("Not a non terminal node: {:?}", node),
    }
}

#[cfg(test)]
pub mod tests {
    use std::{fmt::Write, iter::repeat};

    use crate::{
        core::{
            pos::{InclPosRange, Pos},
            spec::Spec,
        },
        parsing::scanner::Token,
        util::once::OnceQueue,
    };

    use super::*;

    fn code_in_span(span: Span, input: &str) -> &str {
        if span.end().is_some() {
            let end_pos = span.start + span.length;
            &input[span.start..end_pos]
        } else {
            ""
        }
    }

    pub fn tree_repr(tree: &PackedParseForest, input: &str, decl_ids: &IdVec<String>) -> String {
        let mut result = String::new();

        if let Some(id) = tree.root {
            result.push_str(&tree_node_repr(id, 0, tree, input, decl_ids))
        }

        result
    }

    fn tree_node_repr(
        id: TreeNodeId,
        indent_level: usize,
        tree: &PackedParseForest,
        input: &str,
        decl_ids: &IdVec<String>,
    ) -> String {
        let node = &tree[id];
        let repr = match &node.data {
            TreeNodeData::Leaf(_) => indent(code_in_span(node.span, input), indent_level),
            TreeNodeData::NonTerminal(rule, alts) => {
                let alt = indent("Alts", indent_level + 1);
                let mut alts_repr = alts
                    .iter()
                    .map(|&id| tree_node_repr(id, indent_level + 2, tree, input, decl_ids))
                    .collect::<Vec<String>>();
                alts_repr.sort();
                format!(
                    "{}:\n{}:\n{}",
                    indent(&decl_ids[(*rule).into()], indent_level),
                    alt,
                    alts_repr.join("\n")
                )
            }
            TreeNodeData::Constructed(kind, child) => {
                let kind = indent(&decl_ids[(*kind).into()], indent_level);

                child
                    .map(|c| {
                        format!(
                            "{}:\n{}",
                            kind,
                            tree_node_repr(c, indent_level + 1, tree, input, decl_ids)
                        )
                    })
                    .unwrap_or(kind)
            }
            TreeNodeData::Intermediate(child) => {
                tree_node_repr(*child, indent_level, tree, input, decl_ids)
            }
            TreeNodeData::Packed(left, right) => {
                let mut left_repr = tree_node_repr(*left, indent_level, tree, input, decl_ids);
                let right_repr =
                    right.map(|r| tree_node_repr(r, indent_level, tree, input, decl_ids));

                if let Some(r) = right_repr {
                    left_repr.push('\n');
                    left_repr.push_str(&r);
                }

                left_repr
            }
            TreeNodeData::Named(pos, child) => {
                let field_repr = indent(&format!("{pos:?}"), indent_level);
                let child_repr = tree_node_repr(*child, indent_level + 1, tree, input, decl_ids);

                return format!("{field_repr}\n{child_repr}");
            }
            TreeNodeData::Empty => indent("ε", indent_level),
        };

        repr
    }

    pub fn to_dot(tree: &PackedParseForest, input: &str, decls: &IdVec<String>) -> String {
        let mut to_visit = tree
            .root
            .map(|node| OnceQueue::from([node]))
            .unwrap_or_default();
        let mut statements = String::new();

        while let Some(node) = to_visit.pop() {
            writeln!(statements, "\t{}", dot_repr(tree, node, input, decls)).unwrap();

            for child in tree.childs(node) {
                to_visit.push(child);

                writeln!(
                    statements,
                    "\t{:?} -> {:?};",
                    node.0.index_value(),
                    child.0.index_value()
                )
                .unwrap();
            }
        }

        format!("digraph G {{\n{}}}", statements)
    }

    fn dot_repr(
        tree: &PackedParseForest,
        id: TreeNodeId,
        input: &str,
        decls: &IdVec<String>,
    ) -> String {
        let node = &tree[id];

        let shape = match node.data {
            TreeNodeData::Leaf(_) => "plaintext",
            TreeNodeData::Constructed(_, _) => "diamond",
            TreeNodeData::Intermediate(_) => "rectangle",
            TreeNodeData::Packed(_, _) => "point",
            TreeNodeData::NonTerminal(_, _) => "ellipse",
            TreeNodeData::Named(_, _) => "parallelogram",
            TreeNodeData::Empty => "plaintext",
        };

        let label = match node.data {
            TreeNodeData::Leaf(_) => code_in_span(node.span, input).to_string(),
            TreeNodeData::Constructed(kind, _) => {
                let kind_name = decls.get(kind.into()).unwrap().to_string();
                format!("{}({:?})", kind_name, kind)
            }
            TreeNodeData::Intermediate(_) => "<>".to_string(),
            TreeNodeData::NonTerminal(rule, _) => decls.get(rule.into()).unwrap().to_string(),
            TreeNodeData::Packed(_, _) => String::new(),
            TreeNodeData::Named(pos, _) => format!("{pos:?}"),
            TreeNodeData::Empty => "ε".into(),
        };

        format!(
            "{:?} [shape={}, label=\"{}\"]",
            id.0.index_value(),
            shape,
            label
        )
    }

    fn indent(text: impl AsRef<str>, indentation: usize) -> String {
        let indent_str = repeat(". ")
            .take(indentation)
            .collect::<Vec<&str>>()
            .join("");
        format!("{}{}", indent_str, text.as_ref())
    }

    #[test]
    fn terminal_childs() {
        let token = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 2), 2)).unwrap(),
            0.into(),
        );

        let mut forest = PackedParseForest::new();

        let t1 = forest.terminal(token);

        assert!(forest.childs(t1).is_empty());
    }

    #[test]
    fn packed_childs() {
        let token1 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 2), 2)).unwrap(),
            0.into(),
        );
        let token2 = Token::new(
            InclPosRange::new(Pos::new((1, 3), 2), Pos::new((1, 4), 3)).unwrap(),
            0.into(),
        );

        let mut forest = PackedParseForest::new();

        let t1 = forest.terminal(token1);
        let t2 = forest.terminal(token2);
        let intermediate = forest.intermediate(t1, t2).unwrap();

        assert_eq!(1, forest.childs(intermediate).len());

        let packed = forest.childs(intermediate).pop().unwrap();
        assert_eq!(vec![t1, t2], forest.childs(packed));
    }

    #[test]
    fn do_not_pack_if_span_gap() {
        let token1 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 2), 2)).unwrap(),
            0.into(),
        );
        let token2 = Token::new(
            InclPosRange::new(Pos::new((1, 2), 1), Pos::new((1, 4), 3)).unwrap(),
            0.into(),
        );

        let mut forest = PackedParseForest::new();
        let t1 = forest.terminal(token1);
        let t2 = forest.terminal(token2);

        let intermediate = forest.intermediate(t1, t2);

        assert_eq!(None, intermediate);
    }

    #[test]
    fn constructed_childs() {
        let kind: KindId = 0.into();

        let token1 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 2), 1)).unwrap(),
            0.into(),
        );

        let mut forest = PackedParseForest::new();

        let t = forest.terminal(token1);
        let constructed = forest.constructed(0, kind, Some(t));

        assert_eq!(vec![t], forest.childs(constructed));
    }

    #[test]
    fn non_terminal_childs() {
        let rule_id: RuleId = 0.into();
        let kind: KindId = 0.into();
        let kind2: KindId = 1.into();

        let mut forest = PackedParseForest::new();

        let token1 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 2), 1)).unwrap(),
            0.into(),
        );

        let t1 = forest.terminal(token1);
        let constructed = forest.constructed(0, kind, Some(t1));
        let non_term = forest.non_terminal(rule_id, constructed);
        let constructed2 = forest.constructed(0, kind2, Some(t1));
        forest.non_terminal(rule_id, constructed2);

        let childs = forest.childs(non_term);
        assert_eq!(2, childs.len());
        assert!(childs.contains(&constructed));
        assert!(childs.contains(&constructed2));
    }

    #[test]
    fn find_or_add_constructed_created_valid_node() {
        let kind_id: KindId = 0.into();
        let span = Span::new(0, 1);

        let mut forest = PackedParseForest::new();

        let token1 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 2), 1)).unwrap(),
            0.into(),
        );

        let t1 = forest.terminal(token1);
        let n = forest.constructed(0, kind_id, Some(t1));

        assert_eq!(forest[n], TreeNode::constructed(kind_id, Some(t1), span));
    }

    #[test]
    fn find_or_add_constructed_recycles_node() {
        let kind_id: KindId = 0.into();

        let mut forest = PackedParseForest::new();
        let token1 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 2), 1)).unwrap(),
            0.into(),
        );
        let t1 = forest.terminal(token1);

        let n1 = forest.constructed(0, kind_id, Some(t1));
        let n2 = forest.constructed(0, kind_id, Some(t1));

        assert_eq!(n1, n2);
    }

    #[test]
    fn find_or_add_constructed_creates_a_new_node() {
        let kind_id: KindId = 0.into();

        let mut forest = PackedParseForest::new();

        let token1 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 1), 1)).unwrap(),
            0.into(),
        );
        let token2 = Token::new(
            InclPosRange::new(Pos::new((1, 2), 1), Pos::new((1, 2), 2)).unwrap(),
            0.into(),
        );

        let t1 = forest.terminal(token1);
        let t2 = forest.terminal(token2);

        let n1 = forest.constructed(0, kind_id, Some(t1));
        let n2 = forest.constructed(0, kind_id, Some(t2));

        assert_ne!(n1, n2);
    }

    #[test]
    fn create_non_terminal_from_scratch() {
        let rule_id: RuleId = 0.into();
        let span1 = Span::new(0, 1);

        let mut forest = PackedParseForest::new();

        let token1 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 2), 1)).unwrap(),
            0.into(),
        );

        let t1 = forest.terminal(token1);
        let non_term = forest.non_terminal(rule_id, t1);

        assert!(matches!(
            forest[non_term],
            TreeNode { data: TreeNodeData::NonTerminal(s, _), ..} if s == rule_id
        ));

        let childs = forest.childs(non_term);
        assert!(matches!(
            forest[*childs.iter().next().unwrap()],
            TreeNode {
                data: TreeNodeData::Leaf(t),
                span
            } if span == span1 && t == token1
        ));
    }

    #[test]
    fn add_derivation_to_non_terminal() {
        let rule_id: RuleId = 0.into();

        let mut forest = PackedParseForest::new();

        let token1 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 2), 1)).unwrap(),
            0.into(),
        );

        let token2 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 2), 1)).unwrap(),
            1.into(),
        );

        let t1 = forest.terminal(token1);
        let non_term = forest.non_terminal(rule_id, t1);

        let t3 = forest.terminal(token2);
        let non_term2 = forest.non_terminal(rule_id, t3);

        assert_eq!(non_term, non_term2);
        assert_eq!(2, forest.childs(non_term2).len());
    }

    #[test]
    fn find_or_create_terminal_creates_a_terminal_when_needed() {
        let token1 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 1), 1)).unwrap(),
            0.into(),
        );

        let token2 = Token::new(
            InclPosRange::new(Pos::new((1, 2), 1), Pos::new((1, 3), 2)).unwrap(),
            0.into(),
        );

        let mut forest = PackedParseForest::new();

        let t1 = forest.terminal(token1);
        let t2 = forest.terminal(token2);

        assert_ne!(t1, t2);
    }

    #[test]
    fn find_or_create_terminal_reuses_existing_node() {
        let mut forest = PackedParseForest::new();

        let token1 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 2), 1)).unwrap(),
            0.into(),
        );

        let init_id = forest.terminal(token1);

        assert_eq!(init_id, forest.terminal(token1));
    }

    #[test]
    fn find_of_create_intermediate_reuses_intermediate_when_needed() {
        let mut forest = PackedParseForest::new();

        let token1 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 1), 1)).unwrap(),
            0.into(),
        );

        let token2 = Token::new(
            InclPosRange::new(Pos::new((1, 2), 1), Pos::new((1, 3), 2)).unwrap(),
            0.into(),
        );

        let t1 = forest.terminal(token1);
        let t2 = forest.terminal(token2);

        let init_id = forest.intermediate(t1, t2);

        assert_eq!(init_id, forest.intermediate(t1, t2));
    }

    #[test]
    fn find_or_crate_intermediate_creates_a_new_node_when_needed() {
        let mut forest = PackedParseForest::new();

        let token11 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 1), 1)).unwrap(),
            0.into(),
        );

        let token12 = Token::new(
            InclPosRange::new(Pos::new((1, 2), 1), Pos::new((1, 2), 2)).unwrap(),
            0.into(),
        );

        let token21 = Token::new(
            InclPosRange::new(Pos::default(), Pos::new((1, 1), 1)).unwrap(),
            0.into(),
        );

        let token22 = Token::new(
            InclPosRange::new(Pos::new((1, 2), 1), Pos::new((1, 3), 2)).unwrap(),
            0.into(),
        );

        let t11 = forest.terminal(token11);
        let t12 = forest.terminal(token12);
        let t21 = forest.terminal(token21);
        let t22 = forest.terminal(token22);

        let intermediate1 = forest.intermediate(t11, t12);
        let intermediate2 = forest.intermediate(t21, t22);

        assert_ne!(intermediate1, intermediate2);
    }

    pub fn pretty_print_sppf(spec: &Spec, tree: &PackedParseForest, input_str: &str) -> String {
        let decl_names = get_decl_names(spec);

        tree_repr(tree, input_str, &decl_names)
    }

    pub fn get_decl_names(spec: &Spec) -> IdVec<String> {
        (0usize..)
            .map(|n| spec.syntax.decl_from_id(Id::from_index(n)))
            .take_while(|d| d.is_some())
            .map(|d| d.unwrap().name().to_string())
            .collect()
    }
}
