use derive_more::From;
use std::cell::RefCell;
use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
};

use crate::script::ScriptEngine;
use crate::{
    core::spec::Aspects,
    land::{sylva::SylvaId, Land},
    query::SylvaNode,
    script::{python::PythonScriptEngine, ScriptQueryValue, ScriptTreeInfo, ScriptValue},
    tree::info::raw::RawTreeInfo,
};

static SG_GEN_ASPECT: &str = "sg_gen";

pub fn compute_sgraph(
    land: &Land,
    sylva_id: SylvaId,
    aspects: &Aspects,
    mut tree_infos: RawTreeInfo,
    engine: PythonScriptEngine,
) -> Arc<RwLock<SGraph>> {
    let sylva = land.sylva(sylva_id);

    let sgraph = Arc::new(RwLock::new(SGraph::new()));

    let Some(aspect) = aspects.get(SG_GEN_ASPECT) else {
        return sgraph;
    };

    for (tree_id, tree) in sylva.iter() {
        let tree_scope = {
            let mut guard = sgraph.write().expect("poisoned scope graph lock");
            let root = guard.root();
            guard.add_scope(root)
        };

        for node in tree.nodes() {
            if let Some(script) = aspect.get(&tree.tree[node].kind) {
                let node_arg = ScriptQueryValue::Node(SylvaNode {
                    sylva: sylva_id,
                    tree: tree_id,
                    node,
                });

                let tree_infos = RefCell::new(ScriptTreeInfo::new(&mut tree_infos));

                let scope_arg = ScriptQueryValue::Simple(ScriptValue::Scope(
                    tree_scope,
                    sgraph.clone(),
                    tree_infos.clone(),
                ));

                engine.eval_in_query(script, vec![node_arg, scope_arg], tree_infos);
            }
        }
    }

    sgraph
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub struct ScopeId(petgraph::graph::NodeIndex);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum SGraphValue {
    Decl(SylvaNode, String),
    Ref(SylvaNode, String),
}

#[derive(Debug, Clone, Default)]
struct SGraphNode {
    values: Vec<SGraphValue>,
}

impl SGraphNode {
    fn get_decl(&self, name: &str) -> Option<SylvaNode> {
        self.values.iter().find_map(|v| match v {
            SGraphValue::Decl(node, n) if n == name => Some(*node),
            _ => None,
        })
    }

    fn refs(&self) -> impl Iterator<Item = (SylvaNode, &str)> {
        self.values.iter().filter_map(|v| match v {
            SGraphValue::Ref(node, n) => Some((*node, n.as_str())),
            _ => None,
        })
    }
}

#[derive(Debug, Clone, Default)]
pub struct SGraph {
    graph: petgraph::Graph<SGraphNode, ()>,
    decl_to_refs: HashMap<SylvaNode, Vec<SylvaNode>>,
    ref_to_decl: HashMap<SylvaNode, SylvaNode>,
}

impl SGraph {
    pub fn new() -> SGraph {
        let mut graph = petgraph::Graph::new();
        graph.add_node(SGraphNode::default());
        SGraph {
            graph,
            decl_to_refs: HashMap::default(),
            ref_to_decl: HashMap::default(),
        }
    }

    pub fn root(&self) -> ScopeId {
        petgraph::graph::NodeIndex::new(0).into()
    }

    pub fn add_decl(&mut self, scope: ScopeId, name: String, node: SylvaNode) {
        self.add_value(scope, SGraphValue::Decl(node, name));
    }

    pub fn add_ref(&mut self, scope: ScopeId, name: String, node: SylvaNode) {
        self.add_value(scope, SGraphValue::Ref(node, name));
    }

    fn add_value(&mut self, scope: ScopeId, value: SGraphValue) {
        let scope = self.graph.node_weight_mut(scope.0).unwrap();
        scope.values.push(value);
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

                if let Some(n) = current_scope.get_decl(name) {
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

    pub fn solve(&mut self) {
        for scope_id in self.graph.node_indices() {
            let scope = &self.graph[scope_id];

            for (ref_node, name) in scope.refs() {
                if let Some(&referenced_decl) = self.lookup(scope_id.into(), name).first() {
                    self.ref_to_decl.insert(ref_node, referenced_decl);

                    self.decl_to_refs
                        .entry(referenced_decl)
                        .or_default()
                        .push(ref_node);
                }
            }
        }
    }

    pub fn referenced_decls(&self, node: SylvaNode) -> Option<&SylvaNode> {
        self.ref_to_decl.get(&node)
    }

    pub fn node_refs(&self, node: SylvaNode) -> Option<&[SylvaNode]> {
        self.decl_to_refs.get(&node).map(|v| v.as_slice())
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

    #[test]
    pub fn solve() {
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
        let scope2 = graph.add_scope(scope1);
        graph.add_ref(scope2, "foo".to_string(), node2);

        graph.solve();

        assert_eq!(Some(&node1), graph.referenced_decls(node2));
        assert_eq!(Some([node2].as_slice()), graph.node_refs(node1));
    }
}
