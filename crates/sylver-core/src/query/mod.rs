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
            .tree(node.tree)
            .unwrap_or_else(|| panic!("Invalid tree id: {}", node.tree));

        RawTreeInfo::new(tree, &self.spec.syntax)
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum Task {
    Filter(FilterTask),
}

impl Task {
    pub fn run<'b, B: 'b + TreeInfoBuilder<'b>>(
        &self,
        builder: B,
        land: &'b Land,
        sylva_id: SylvaId,
    ) -> Result<Vec<expr::Value<'b>>, expr::EvalError> {
        match self {
            Task::Filter(f) => f.run_(builder, land, sylva_id),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub struct FilterTask {
    expr: Expr,
}

impl FilterTask {
    pub fn new(expr: Expr) -> FilterTask {
        FilterTask { expr }
    }

    /*pub fn run<'b, B: 'b + TreeInfoBuilder<'b>>(
        &self,
        ctx: &mut EvalCtx<'b, B>,
        nodes: impl Iterator<Item = NodeId>,
    ) -> Result<Vec<Value<'b>>, EvalError> {
        let mut result = vec![];

        for node in nodes {
            ctx.push_var(Value::Node(node));
            let evaluated = self.expr.eval(ctx)?;
            ctx.pop_var();

            if evaluated.try_into()? {
                result.push(Value::Node(node));
            }
        }

        Ok(result)
    }*/

    pub fn run_<'b, B: 'b + TreeInfoBuilder<'b>>(
        &self,
        builder: B,
        land: &'b Land,
        sylva_id: SylvaId,
    ) -> Result<Vec<Value<'b>>, EvalError> {
        let spec = land.sylva_spec(sylva_id);

        let mut ctx = EvalCtx::new(spec, builder);
        let mut results = vec![];

        for sylva_node in sylva_nodes(land, sylva_id) {
            ctx.push_var(Value::Node(sylva_node));

            if self.expr.eval(&mut ctx)?.try_into()? {
                results.push(Value::Node(sylva_node));
            }

            ctx.pop_var();
        }

        Ok(results)
    }
}

fn sylva_nodes(land: &'_ Land, sylva: SylvaId) -> impl '_ + Iterator<Item = SylvaNode> {
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
