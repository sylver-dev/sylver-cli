use derive_more::From;
use rustc_hash::FxHashMap;

use crate::query::SylvaNode;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub struct ScopeId(petgraph::graph::NodeIndex);

#[derive(Debug, Clone, Default)]
struct SGraphNode {
    declarations: FxHashMap<String, SylvaNode>,
}

#[derive(Debug, Clone, Default)]
pub struct SGraph {
    graph: petgraph::Graph<SGraphNode, ()>,
}

impl SGraph {
    pub fn new() -> SGraph {
        let mut graph = petgraph::Graph::new();
        graph.add_node(SGraphNode::default());
        SGraph { graph }
    }

    pub fn root(&self) -> ScopeId {
        petgraph::graph::NodeIndex::new(0).into()
    }

    pub fn add_decl(&mut self, scope: ScopeId, name: String, node: SylvaNode) {
        let scope = self.graph.node_weight_mut(scope.0).unwrap();
        scope.declarations.insert(name, node);
    }

    pub fn add_scope(&mut self, scope: ScopeId) -> ScopeId {
        let new_scope = self.graph.add_node(SGraphNode::default());
        self.graph.add_edge(new_scope, scope.0, ());
        new_scope.into()
    }

    pub fn connect_scope(&mut self, origin: ScopeId, target: ScopeId) {
        self.graph.add_edge(origin.0, target.0, ());
    }

    pub fn lookup(&self, scope: ScopeId, name: &str) -> Vec<SylvaNode> {
        let mut nodes = vec![];
        let mut to_visit = vec![scope.0];

        while !to_visit.is_empty() && nodes.is_empty() {
            for scope_id in std::mem::take(&mut to_visit) {
                let current_scope = self.graph.node_weight(scope_id).unwrap();

                if let Some(&n) = current_scope.declarations.get(name) {
                    nodes.push(n);
                } else {
                    to_visit.extend(
                        self.graph
                            .neighbors_directed(scope_id, petgraph::Direction::Outgoing),
                    );
                }
            }
        }

        nodes
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use maplit::hashset;

    #[test]
    fn lookup_missing() {
        let mut graph = SGraph::new();

        graph.add_decl(
            graph.root(),
            "foo".to_string(),
            SylvaNode {
                sylva: 0.into(),
                tree: 0.into(),
                node: 0.into(),
            },
        );

        let expected: Vec<SylvaNode> = vec![];

        assert_eq!(expected, graph.lookup(graph.root(), "bar"))
    }

    #[test]
    fn lookup_trivial() {
        let node = SylvaNode {
            sylva: 0.into(),
            tree: 0.into(),
            node: 0.into(),
        };

        let mut graph = SGraph::new();

        graph.add_decl(graph.root(), "foo".to_string(), node);

        let expected = vec![node];

        assert_eq!(expected, graph.lookup(graph.root(), "foo"));
    }

    #[test]
    fn lookup_nested() {
        let shadowed_node = SylvaNode {
            sylva: 0.into(),
            tree: 0.into(),
            node: 0.into(),
        };

        let node = SylvaNode {
            sylva: 0.into(),
            tree: 0.into(),
            node: 1.into(),
        };

        let mut graph = SGraph::new();
        graph.add_decl(graph.root(), "foo".to_string(), shadowed_node);
        let nested_scope = graph.add_scope(graph.root());
        graph.add_decl(nested_scope, "foo".to_string(), node);

        let expected_nested = vec![node];
        assert_eq!(expected_nested, graph.lookup(nested_scope, "foo"));

        let expected_root = vec![shadowed_node];
        assert_eq!(expected_root, graph.lookup(graph.root(), "foo"));
    }

    #[test]
    fn lookup_multiple() {
        let node1 = SylvaNode {
            sylva: 0.into(),
            tree: 0.into(),
            node: 0.into(),
        };

        let node2 = SylvaNode {
            sylva: 0.into(),
            tree: 0.into(),
            node: 1.into(),
        };

        let mut graph = SGraph::new();
        let scope1 = graph.add_scope(graph.root());
        graph.add_decl(scope1, "foo".to_string(), node1);
        let scope2 = graph.add_scope(graph.root());
        graph.add_decl(scope2, "foo".to_string(), node2);

        let scope3 = graph.add_scope(scope1);
        graph.connect_scope(scope3, scope2);

        let expected = hashset![node1, node2];

        assert_eq!(
            expected,
            graph
                .lookup(scope3, "foo")
                .into_iter()
                .collect::<std::collections::HashSet<_>>()
        );
    }
}
