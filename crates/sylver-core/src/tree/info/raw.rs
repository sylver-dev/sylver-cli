use crate::{
    core::{
        pos::InclPosRange,
        source::SourceTree,
        spec::{FieldPos, KindId, Syntax, TagId},
    },
    parsing::{scanner::Token, sppf::TokenPos},
    tree::{Node, NodeId},
};

use super::{NodeProxy, TreeInfo};

#[derive(Debug, Clone, Copy)]
pub struct RawTreeInfo<'t> {
    source: &'t SourceTree,
    syntax: &'t Syntax,
}

impl<'t> RawTreeInfo<'t> {
    pub fn new(source: &'t SourceTree, syntax: &'t Syntax) -> Self {
        RawTreeInfo { source, syntax }
    }
}

impl<'t> TreeInfo<'t> for RawTreeInfo<'t> {
    fn node_ids(&self) -> Box<dyn 't + Iterator<Item = NodeId>> {
        Box::new(self.source.tree.bottom_up_node_ids())
    }

    fn root(&self) -> NodeProxy<Self> {
        self.proxy(self.source.tree.root)
    }

    fn proxy(&self, id: NodeId) -> NodeProxy<Self> {
        if self.source.tree.get_node(id).is_none() {
            panic!("Missing node for id {id:?}")
        }

        NodeProxy { id, infos: *self }
    }

    fn comment_kind(&self) -> KindId {
        self.syntax.comment_kind()
    }

    fn ignore_tags(&self) -> &[TagId] {
        self.syntax.ignore_tags()
    }

    fn token_code(&self, token: Token) -> &str {
        self.source.code_between(token, token)
    }

    fn field_name(&self, kind: KindId, field: FieldPos) -> Option<&str> {
        self.syntax.field_name(kind, field)
    }

    fn field_value(&self, node_id: NodeId, field: FieldPos) -> Option<NodeId> {
        let node = self.node(node_id);
        node.named_childs[Into::<usize>::into(field)].map(|child_pos| node.childs[child_pos])
    }

    fn kind_name(&self, kind: KindId) -> &str {
        self.syntax.kind_name(kind)
    }

    fn parent(&self, node: NodeId) -> Option<NodeId> {
        self.node(node).parent
    }

    fn node(&self, node: NodeId) -> &'t Node {
        &self.source.tree[node]
    }

    fn node_tokens(&self, node: NodeId) -> &'t [Token] {
        self.source.node_tokens_with_ignore(node)
    }

    fn node_text(&self, node: NodeId) -> &'t str {
        self.source.node_text(node, self.syntax.trivial_tags())
    }

    fn node_code(&self, node: NodeId) -> &'t str {
        self.source.node_code(node)
    }

    fn node_pos(&self, node_id: NodeId) -> InclPosRange {
        let node = self.node(node_id);

        let (first, last) = if node.span.length == 0 {
            // We can emit 0-sized nodes right after the last token (for example, an empty list...).
            // In this case, fetch the position from the last token.
            let token_pos = TokenPos::min(self.source.tokens.len() - 1, node.span.start);
            let token = self.source.existing_token(token_pos);
            (token, token)
        } else {
            let tokens = self.source.node_tokens_with_ignore(node_id);
            let start = tokens.first().unwrap();
            let end = tokens.last().unwrap();
            (start, end)
        };

        InclPosRange::new(first.pos.start(), last.pos.end()).unwrap()
    }
}
