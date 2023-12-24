use std::collections::VecDeque;

use itertools::Itertools;
use smallvec::SmallVec;

use crate::{
    core::{
        pos::InclPosRange,
        spec::{FieldPos, KindId, TagId},
    },
    parsing::scanner::Token,
    tree::{Node, NodeId},
    util::{depth_iter::DepthVal, once::OnceQueue},
};

pub mod raw;

pub trait TreeInfo<'t>: Sized {
    fn node_ids(&'_ self) -> Box<dyn 't + Iterator<Item = NodeId>>;

    fn root(&self) -> NodeProxy<Self>;

    fn proxy(&self, id: NodeId) -> NodeProxy<Self>;

    fn comment_kind(&self) -> KindId;

    fn ignore_tags(&self) -> &[TagId];

    fn token_code(&self, token: Token) -> &str;

    fn field_name(&self, kind: KindId, field: FieldPos) -> Option<&str>;

    fn field_value(&self, node: NodeId, field: FieldPos) -> Option<NodeId>;
    
    fn field_value_from_name(&self, node: NodeId, field_name: &str) -> Option<NodeId>;

    fn kind_name(&self, kind: KindId) -> &str;

    fn parent(&self, node: NodeId) -> Option<NodeId>;

    /// Position among the node's siblings.
    fn parent_pos(&self, node: NodeId) -> usize {
        let parent = if let Some(p) = self.parent(node) {
            p
        } else {
            return 0;
        };

        self.node(parent)
            .childs
            .iter()
            .position(|&n| n == node)
            .unwrap_or_default()
    }

    fn prev_sibling(&self, node_id: NodeId) -> Option<NodeId> {
        let node = self.node(node_id);
        self.node(node.parent?)
            .childs
            .iter()
            .tuple_windows()
            .find_map(|(&prev, &n)| if n == node_id { Some(prev) } else { None })
    }

    fn next_sibling(&self, node_id: NodeId) -> Option<NodeId> {
        let node = self.node(node_id);
        self.node(node.parent?)
            .childs
            .iter()
            .tuple_windows()
            .find_map(|(&n, &next)| if n == node_id { Some(next) } else { None })
    }

    fn descendants(&self, node: NodeId) -> Vec<NodeId> {
        let mut res = vec![];
        let mut queue = OnceQueue::from_iter(self.node(node).childs.iter().copied());

        while let Some(n) = queue.pop() {
            res.push(n);
            queue.extend(self.node(n).childs.iter().copied());
        }

        res
    }

    fn node(&self, node: NodeId) -> &'t Node;

    fn node_tokens(&self, node: NodeId) -> &'t [Token];

    fn node_text(&self, node: NodeId) -> &'t str;

    fn node_code(&self, node: NodeId) -> &'t str;

    fn node_pos(&self, node: NodeId) -> InclPosRange;
}

/// Return the non comment nodes under the given node.
pub fn non_comment_childs<'t, T: TreeInfo<'t>>(tree: &T, node: &NodeProxy<T>) -> Vec<NodeProxy<T>> {
    filter_childs(node, |n| n.node().kind != tree.comment_kind())
}

/// Return the comment nodes under the given node.
pub fn comment_childs<'t, T: TreeInfo<'t>>(tree: &T, node: &NodeProxy<T>) -> Vec<NodeProxy<T>> {
    filter_childs(node, |n| n.node().kind == tree.comment_kind())
}

fn filter_childs<'t, T: TreeInfo<'t>>(
    node: &NodeProxy<T>,
    predicate: impl Fn(&NodeProxy<T>) -> bool,
) -> Vec<NodeProxy<T>> {
    node.direct_children()
        .into_iter()
        .filter(predicate)
        .collect()
}

#[derive(Debug, Clone, Copy)]
pub struct NodeProxy<T> {
    /// Id of the tree node represented by this proxy.
    /// A proxy should never be built for a non existing node.
    pub id: NodeId,
    /// Underlying tree infos.
    pub infos: T,
}

impl<'t, T: TreeInfo<'t>> NodeProxy<T> {
    /// Return the id of the proxied node.
    pub fn id(&self) -> NodeId {
        self.id
    }

    /// Return the name of the nth child of the current node, if it exists.
    fn nth_children_field_name(&self, n: usize) -> Option<&str> {
        let field_pos = self.node().nth_child_field_pos(n)?;
        self.infos.field_name(self.node().kind, field_pos)
    }

    pub fn node(&self) -> &'t Node {
        self.infos.node(self.id)
    }

    pub fn kind_name(&self) -> &str {
        self.infos.kind_name(self.node().kind)
    }

    pub fn direct_children(&self) -> SmallVec<[Self; 6]> {
        SmallVec::from_iter(self.node().childs.iter().map(|&id| self.infos.proxy(id)))
    }

    pub fn children_with_name(&self) -> SmallVec<[(Option<&str>, Self); 6]> {
        self.direct_children()
            .into_iter()
            .enumerate()
            .map(|(n, child)| (self.nth_children_field_name(n), child))
            .collect()
    }

    pub fn tokens(&self) -> &'t [Token] {
        self.infos.node_tokens(self.id)
    }

    pub fn code(&self) -> &'t str {
        self.infos.node_code(self.id)
    }

    pub fn contains_token(&self, token: Token) -> bool {
        match (self.tokens().first(), self.tokens().last()) {
            (Some(first), Some(last)) => {
                first.pos.start() <= token.pos.start() && last.pos.end() >= token.pos.end()
            }
            _ => false,
        }
    }
}

pub struct NodeProxyChilds<T> {
    queue: VecDeque<DepthVal<NodeProxy<T>>>,
}

impl<'t, T: TreeInfo<'t>> NodeProxyChilds<T> {
    pub fn new(node: NodeProxy<T>) -> Self {
        let init_val = DepthVal {
            val: node,
            depth: 0,
        };

        NodeProxyChilds {
            queue: VecDeque::from([init_val]),
        }
    }
}

impl<'t, T: TreeInfo<'t>> Iterator for NodeProxyChilds<T> {
    type Item = DepthVal<NodeProxy<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        let elem = self.queue.pop_front()?;

        for child in elem.val.direct_children() {
            self.queue.push_back(DepthVal {
                val: child,
                depth: elem.depth + 1,
            })
        }

        Some(elem)
    }
}

#[cfg(test)]
pub mod tests {
    use std::cmp::max;
    use std::collections::HashMap;

    use maplit::hashmap;

    use crate::{parsing::sppf::Span, tree::NodeId};

    use super::*;

    #[derive(Debug)]
    pub struct TestTree {
        id: NodeId,
        kind: KindId,
        childs: Vec<TestTree>,
    }

    impl TestTree {
        pub fn node(id: NodeId, kind: KindId, childs: Vec<TestTree>) -> TestTree {
            TestTree { id, kind, childs }
        }

        pub fn leaf(id: NodeId, kind: KindId) -> TestTree {
            TestTree {
                id,
                kind,
                childs: vec![],
            }
        }
    }

    #[derive(Debug, Eq, PartialEq, Clone)]
    pub struct TestTreeInfo<'t> {
        root: NodeId,
        nodes: &'t HashMap<NodeId, Node>,
        nodes_code: &'t HashMap<NodeId, String>,
    }

    impl<'t> TestTreeInfo<'t> {
        pub fn new(
            nodes: &'t mut HashMap<NodeId, Node>,
            nodes_code: &'t mut HashMap<NodeId, String>,
            root: NodeId,
        ) -> TestTreeInfo<'t> {
            TestTreeInfo {
                root,
                nodes,
                nodes_code,
            }
        }

        pub fn from_tree(
            root: TestTree,
            nodes: &'t mut HashMap<NodeId, Node>,
            nodes_code: &'t mut HashMap<NodeId, String>,
        ) -> TestTreeInfo<'t> {
            Self::fill_nodes(0, &root, nodes);

            let info = TestTreeInfo {
                root: root.id,
                nodes,
                nodes_code,
            };

            info
        }

        fn fill_nodes(offset: usize, tree: &TestTree, nodes: &mut HashMap<NodeId, Node>) -> usize {
            let mut current_offset = offset;

            for child in &tree.childs {
                current_offset += Self::fill_nodes(current_offset, child, nodes);
                nodes.get_mut(&child.id).unwrap().parent = Some(tree.id);
            }

            nodes.insert(
                tree.id,
                Node {
                    kind: tree.kind,
                    span: Span::new(offset, max(current_offset, 1)),
                    parent: None,
                    named_childs: vec![],
                    childs: tree.childs.iter().map(|c| c.id).collect(),
                },
            );

            max(current_offset, 1)
        }
    }

    impl<'t> TreeInfo<'t> for TestTreeInfo<'t> {
        fn node_ids(&'_ self) -> Box<dyn 't + Iterator<Item = NodeId>> {
            Box::new(self.nodes.keys().copied())
        }

        fn root(&self) -> NodeProxy<Self> {
            self.proxy(self.root)
        }

        fn proxy(&self, id: NodeId) -> NodeProxy<Self> {
            NodeProxy {
                id,
                infos: self.clone(),
            }
        }

        fn comment_kind(&self) -> KindId {
            todo!()
        }

        fn ignore_tags(&self) -> &[TagId] {
            todo!()
        }

        fn token_code(&self, _token: Token) -> &str {
            todo!()
        }

        fn field_name(&self, _kind: KindId, _field: FieldPos) -> Option<&str> {
            todo!()
        }

        fn field_value(&self, node_id: NodeId, field: FieldPos) -> Option<NodeId> {
            let node = self.node(node_id);
            node.named_childs[Into::<usize>::into(field)]
                .map(|child_index| node.childs[child_index])
        }

        fn kind_name(&self, _kind: KindId) -> &str {
            todo!()
        }

        fn parent(&self, node: NodeId) -> Option<NodeId> {
            self.nodes.get(&node)?.parent
        }

        fn node(&self, node: NodeId) -> &'t Node {
            self.nodes.get(&node).unwrap()
        }

        fn node_tokens(&self, _node: NodeId) -> &'t [Token] {
            todo!()
        }

        fn node_text(&self, node: NodeId) -> &'t str {
            &self.nodes_code[&node]
        }

        fn node_code(&self, node: NodeId) -> &'t str {
            &self.nodes_code[&node]
        }

        fn node_pos(&self, _node: NodeId) -> InclPosRange {
            todo!()
        }
    }

    #[test]
    fn from_tree() {
        let root_id: NodeId = 0.into();
        let root_kind: KindId = 1.into();

        let child1_id: NodeId = 2.into();
        let child2_id: NodeId = 3.into();
        let child_kind: KindId = 4.into();

        let mut nodes = HashMap::new();
        let mut nodes_code = HashMap::new();

        let info = TestTreeInfo::from_tree(
            TestTree::node(
                root_id,
                root_kind,
                vec![
                    TestTree::leaf(child1_id, child_kind),
                    TestTree::leaf(child2_id, child_kind),
                ],
            ),
            &mut nodes,
            &mut nodes_code,
        );

        assert_eq!(info.root, root_id);

        assert_eq!(
            info.nodes,
            &hashmap! {
                root_id => Node {
                    kind: root_kind,
                    span: Span::new(0, 2),
                    parent: None,
                    named_childs: vec![],
                    childs: vec![child1_id, child2_id],
                },
                child1_id => Node {
                    kind: child_kind,
                    span: Span::new(0, 1),
                    parent: Some(root_id),
                    named_childs: vec![],
                    childs: vec![],
                },
                child2_id => Node {
                    kind: child_kind,
                    span: Span::new(1, 1),
                    parent: Some(root_id),
                    named_childs: vec![],
                    childs: vec![],
                },
            }
        );
    }

    #[test]
    fn prev_sibling() {
        let parent_id: NodeId = 0.into();

        let child1_id: NodeId = 1.into();
        let child1 = Node {
            kind: 0.into(),
            span: Span::new(0, 1),
            parent: Some(parent_id),
            named_childs: vec![],
            childs: vec![],
        };

        let child2_id: NodeId = 2.into();
        let child2 = Node {
            kind: 0.into(),
            span: Span::new(1, 1),
            parent: Some(parent_id),
            named_childs: vec![],
            childs: vec![],
        };

        let child3_id: NodeId = 3.into();
        let child3 = Node {
            kind: 0.into(),
            span: Span::new(2, 1),
            parent: Some(parent_id),
            named_childs: vec![],
            childs: vec![],
        };

        let parent_node = Node {
            kind: 0.into(),
            span: Span::new(0, 3),
            parent: None,
            named_childs: vec![],
            childs: vec![child1_id, child2_id, child3_id],
        };

        let mut nodes = hashmap! {
            parent_id => parent_node,
            child1_id => child1,
            child2_id => child2,
            child3_id => child3
        };
        let mut nodes_code = HashMap::new();

        let info = TestTreeInfo::new(&mut nodes, &mut nodes_code, parent_id);

        assert_eq!(None, info.prev_sibling(child1_id));
        assert_eq!(Some(child1_id), info.prev_sibling(child2_id));
        assert_eq!(Some(child2_id), info.prev_sibling(child3_id));
    }

    #[test]
    fn next_sibling() {
        let parent_id: NodeId = 0.into();

        let child1_id: NodeId = 1.into();
        let child1 = Node {
            kind: 0.into(),
            span: Span::new(0, 1),
            parent: Some(parent_id),
            named_childs: vec![],
            childs: vec![],
        };

        let child2_id: NodeId = 2.into();
        let child2 = Node {
            kind: 0.into(),
            span: Span::new(1, 1),
            parent: Some(parent_id),
            named_childs: vec![],
            childs: vec![],
        };

        let child3_id: NodeId = 3.into();
        let child3 = Node {
            kind: 0.into(),
            span: Span::new(2, 1),
            parent: Some(parent_id),
            named_childs: vec![],
            childs: vec![],
        };

        let parent_node = Node {
            kind: 0.into(),
            span: Span::new(0, 3),
            parent: None,
            named_childs: vec![],
            childs: vec![child1_id, child2_id, child3_id],
        };

        let mut nodes = hashmap! {
            parent_id => parent_node,
            child1_id => child1,
            child2_id => child2,
            child3_id => child3
        };
        let mut nodes_code = HashMap::new();

        let info = TestTreeInfo::new(&mut nodes, &mut nodes_code, parent_id);

        assert_eq!(Some(child2_id), info.next_sibling(child1_id));
        assert_eq!(Some(child3_id), info.next_sibling(child2_id));
        assert_eq!(None, info.next_sibling(child3_id));
    }
}
