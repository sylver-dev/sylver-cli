use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    sync::{Arc, RwLock},
};

use derive_more::From;
use thiserror::Error;

use crate::{
    core::spec::Aspects,
    land::{sylva::SylvaTreeId, Land},
    query::SylvaNode,
    script::{
        python::PythonScriptEngine, ScriptEngine, ScriptError, ScriptQueryValue, ScriptTreeInfo,
        ScriptValue,
    },
    tree::info::raw::RawTreeInfo,
};

static SG_GEN_ASPECT: &str = "sg_gen";

#[derive(Debug, Clone, Error)]
pub enum NamesError {
    #[error("unexpected return valued type when executing a name resolution function")]
    UnexpectedEvalType,
    #[error("script error: {0}")]
    Script(#[from] ScriptError),
}

pub struct SylvaSGraph {
    sgraph: SGraph,
    computed_trees: HashSet<SylvaTreeId>,
}

impl SylvaSGraph {
    pub fn new() -> SylvaSGraph {
        SylvaSGraph {
            sgraph: SGraph::new(),
            computed_trees: HashSet::new(),
        }
    }

    pub fn referenced_decls(
        &mut self,
        sylva_node: SylvaNode,
        land: &Land,
        aspects: &Aspects,
        tree_infos: RawTreeInfo,
        engine: PythonScriptEngine,
    ) -> Result<Option<&[SylvaNode]>, NamesError> {
        if self.computed_trees.contains(&sylva_node.tree) {
            return Ok(self.sgraph.referenced_decls(sylva_node));
        }

        self.compute_tree_graph(sylva_node, land, aspects, tree_infos, engine)
    }

    pub fn compute_tree_graph(
        &mut self,
        sylva_node: SylvaNode,
        land: &Land,
        aspects: &Aspects,
        mut tree_infos: RawTreeInfo,
        engine: PythonScriptEngine,
    ) -> Result<Option<&[SylvaNode]>, NamesError> {
        self.computed_trees.insert(sylva_node.tree);

        let sylva = land.sylva(sylva_node.sylva);
        let Some(gen_aspect) = aspects.get(SG_GEN_ASPECT) else {
            return Ok(None);
        };
        let Some(tree) = sylva.tree(sylva_node.tree) else {
            return Ok(None);
        };
        let tree_scope = self.sgraph.add_scope(self.sgraph.root());
        let mut sgraph = Arc::new(RwLock::new(std::mem::take(&mut self.sgraph)));

        for node in tree.nodes() {
            if let Some(script) = gen_aspect.get(&tree.tree[node].kind) {
                let node_arg = ScriptQueryValue::Node(SylvaNode {
                    sylva: sylva_node.sylva,
                    tree: sylva_node.tree,
                    node,
                });

                let tree_infos = RefCell::new(ScriptTreeInfo::new(&mut tree_infos));

                let scope_arg = ScriptQueryValue::Simple(ScriptValue::Scope(
                    tree_scope,
                    sgraph.clone(),
                    tree_infos.clone(),
                ));

                sgraph =
                    match engine.eval_in_query(script, vec![node_arg, scope_arg], tree_infos)? {
                        ScriptQueryValue::Simple(ScriptValue::Scope(_, sgraph, _)) => sgraph,
                        _ => return Err(NamesError::UnexpectedEvalType),
                    };
            }
        }

        let mut sgraph = Arc::into_inner(sgraph)
            .expect("scope graph reference was kept in the script engine")
            .into_inner()
            .expect("poisoned scope graph lock");

        sgraph.solve();

        self.sgraph = sgraph;
        Ok(self.sgraph.referenced_decls(sylva_node))
    }
}

impl Default for SylvaSGraph {
    fn default() -> Self {
        Self::new()
    }
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
    ref_to_decl: HashMap<SylvaNode, Vec<SylvaNode>>,
    dirty_indices: HashSet<ScopeId>,
}

impl SGraph {
    pub fn new() -> SGraph {
        let mut graph = petgraph::Graph::new();
        graph.add_node(SGraphNode::default());
        SGraph {
            graph,
            decl_to_refs: HashMap::default(),
            ref_to_decl: HashMap::default(),
            dirty_indices: HashSet::default(),
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
        let new_scope: ScopeId = self.graph.add_node(SGraphNode::default()).into();

        self.graph.add_edge(new_scope.0, scope.0, ());
        self.dirty_indices.insert(new_scope);

        new_scope
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
        for scope_id in std::mem::take(&mut self.dirty_indices) {
            let scope = &self.graph[scope_id.0];

            for (ref_node, name) in scope.refs() {
                let referenced_decls = self.lookup(scope_id, name);

                for decl in &referenced_decls {
                    self.decl_to_refs.entry(*decl).or_default().push(ref_node);
                }

                self.ref_to_decl.insert(ref_node, referenced_decls);
            }
        }
    }

    pub fn referenced_decls(&self, node: SylvaNode) -> Option<&[SylvaNode]> {
        self.ref_to_decl.get(&node).map(AsRef::as_ref)
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

        assert_eq!(Some([node1].as_slice()), graph.referenced_decls(node2));
        assert_eq!(Some([node2].as_slice()), graph.node_refs(node1));
    }
}
