pub mod expr;
pub mod language;

use crate::{
    core::spec::Spec,
    land::{
        sylva::{Sylva, SylvaId, SylvaTreeId},
        Land,
    },
    tree::{info::raw::RawTreeInfo, info::TreeInfo, NodeId},
};

use expr::{EvalCtx, EvalError, Expr, Value};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct SylvaNode {
    pub sylva: SylvaId,
    pub tree: SylvaTreeId,
    pub node: NodeId,
}

impl SylvaNode {
    pub fn with_node_id(&self, id: NodeId) -> SylvaNode {
        SylvaNode {
            node: id,
            tree: self.tree,
            sylva: self.sylva,
        }
    }
}

pub trait TreeInfoBuilder<'t> {
    type Tree: TreeInfo<'t>;

    fn info_for_node(&self, node: SylvaNode) -> Self::Tree;
}

#[derive(Debug, Clone)]
pub struct RawTreeInfoBuilder<'s> {
    spec: &'s Spec,
    sylva: &'s Sylva,
}

impl<'s> RawTreeInfoBuilder<'s> {
    pub fn new(spec: &'s Spec, sylva: &'s Sylva) -> Self {
        RawTreeInfoBuilder { spec, sylva }
    }
}

impl<'s> TreeInfoBuilder<'s> for RawTreeInfoBuilder<'s> {
    type Tree = RawTreeInfo<'s>;

    fn info_for_node(&self, node: SylvaNode) -> RawTreeInfo<'s> {
        let tree = self
            .sylva
            .source_tree(node.tree)
            .unwrap_or_else(|| panic!("Invalid tree id: {}", node.tree));

        RawTreeInfo::new(tree, &self.spec.syntax)
    }
}

pub fn eval_predicate<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    node: SylvaNode,
    predicate: &Expr,
) -> Result<bool, EvalError> {
    ctx.push_var(Value::Node(node));

    let res = predicate.eval(ctx).and_then(|v| v.try_into())?;

    ctx.pop_var();

    Ok(res)
}

pub fn sylva_nodes(land: &'_ Land, sylva: SylvaId) -> impl '_ + Iterator<Item = SylvaNode> {
    land.sylva(sylva).iter().flat_map(move |(tree_id, tree)| {
        tree.nodes().map(move |node| SylvaNode {
            sylva,
            tree: tree_id,
            node,
        })
    })
}

#[cfg(test)]
pub mod test {
    use super::*;
    use std::collections::HashMap;

    use crate::tree::info::tests::TestTreeInfo;

    #[derive(Clone, Default)]
    pub struct TestTreeInfoBuilder<'t> {
        pub infos: HashMap<SylvaNode, TestTreeInfo<'t>>,
    }

    impl<'t> TreeInfoBuilder<'t> for TestTreeInfoBuilder<'t> {
        type Tree = TestTreeInfo<'t>;

        fn info_for_node(&self, node: SylvaNode) -> Self::Tree {
            self.infos.get(&node).unwrap().clone()
        }
    }
}
