use std::{
    collections::{HashMap, HashSet, VecDeque},
    iter::once,
    ops::{Index, IndexMut},
};

use anyhow::anyhow;
use derive_more::{From, Into};
use itertools::Itertools;
use non_empty_vec::NonEmpty;
use petgraph::prelude::*;
use rustc_hash::FxHashSet;

use crate::{
    core::spec::{FieldPos, KindId, RuleId, Syntax, TagVec},
    util::once::OnceQueue,
};

use sylver_dsl::meta::*;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct GrammarNode {
    pub data: GrammarNodeData,
    pub first: HashSet<TagVec>,
    pub follow: HashSet<TagVec>,
    pub optional: bool,
    pub field: Option<FieldPos>,
}

impl GrammarNode {
    pub fn from_data(data: GrammarNodeData) -> GrammarNode {
        // TODO: Nodes and non-terminals should not have a first and follow set.
        GrammarNode {
            data,
            first: HashSet::new(),
            follow: HashSet::new(),
            optional: false,
            field: None,
        }
    }

    fn is_end_marker(&self) -> bool {
        matches!(
            self,
            GrammarNode {
                data: GrammarNodeData::EndMarker,
                ..
            }
        )
    }
}

impl From<GrammarNodeData> for GrammarNode {
    fn from(data: GrammarNodeData) -> Self {
        GrammarNode::from_data(data)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GrammarNodeData {
    NonTerminal(RuleId),
    Node(KindId, Option<usize>, Option<Associativity>),
    Terminal(TagVec),
    Proxy,
    EndMarker,
}

impl GrammarNodeData {
    pub fn as_node(&self) -> Option<(KindId, Option<usize>, Option<Associativity>)> {
        match self {
            GrammarNodeData::Node(kind, precedence, assoc) => Some((*kind, *precedence, *assoc)),
            _ => None,
        }
    }

    pub fn as_non_terminal(&self) -> Option<RuleId> {
        match self {
            GrammarNodeData::NonTerminal(rule_id) => Some(*rule_id),
            _ => None,
        }
    }

    pub fn is_end_marker(&self) -> bool {
        matches!(self, GrammarNodeData::EndMarker)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum GrammarEdge {
    Child,
    Sibling,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Default, PartialOrd, Ord, From, Into)]
pub struct GrammarElem(NodeIndex);

impl GrammarElem {
    pub fn index(&self) -> usize {
        self.0.index()
    }
}

impl From<usize> for GrammarElem {
    fn from(val: usize) -> Self {
        GrammarElem(NodeIndex::new(val))
    }
}

#[derive(Debug, Clone)]
pub struct Grammar {
    graph: Graph<GrammarNode, GrammarEdge>,
    sibling_rules: HashMap<RuleId, NonEmpty<RuleId>>,
    rule_elems: HashMap<RuleId, GrammarElem>,
    pub goal: GrammarElem,
}

impl Grammar {
    pub fn elems(&self) -> impl Iterator<Item = GrammarElem> {
        self.graph.node_indices().map(Into::into)
    }

    pub fn elem_data(&self, elem: GrammarElem) -> &GrammarNodeData {
        &self[elem].data
    }

    pub fn first_parent(&self, elem: GrammarElem) -> Option<GrammarElem> {
        self.parents(elem).next()
    }

    pub fn parents(&'_ self, elem: GrammarElem) -> impl '_ + Iterator<Item = GrammarElem> {
        self.graph
            .edges_directed(elem.into(), Incoming)
            .filter(|e| e.weight() == &GrammarEdge::Child)
            .map(|e| e.source().into())
    }

    pub fn existing_first_child(&self, elem: GrammarElem) -> GrammarElem {
        self.childs(elem).next().unwrap()
    }

    pub fn childs(&'_ self, elem: GrammarElem) -> impl '_ + Iterator<Item = GrammarElem> {
        self.graph
            .edges_directed(elem.into(), Outgoing)
            .filter(|e| e.weight() == &GrammarEdge::Child)
            .map(|e| e.target())
            .map(GrammarElem)
    }

    pub fn next_sibling(&self, elem: GrammarElem) -> Option<GrammarElem> {
        self.graph
            .edges_directed(elem.into(), Outgoing)
            .filter(|e| e.weight() == &GrammarEdge::Sibling)
            .map(|e| e.target().into())
            .next()
    }

    pub fn end_markers_with_precedence(&self) -> HashMap<usize, FxHashSet<GrammarElem>> {
        let mut result: HashMap<usize, FxHashSet<GrammarElem>> = HashMap::new();

        let end_marker_with_precedence = self
            .graph
            .node_indices()
            .map(Into::<GrammarElem>::into)
            .filter(|&id| self[id].is_end_marker())
            .filter_map(|id| self.node_child_precedence(id).map(|p| (p, id)));

        for (precedence, elem) in end_marker_with_precedence {
            result.entry(precedence).or_default().insert(elem);
        }

        result
    }

    pub fn node_child_precedence(&self, elem: GrammarElem) -> Option<usize> {
        let node_elem = self.first_parent(elem).unwrap();
        let (_, precedence, _) = self[node_elem]
            .data
            .as_node()
            .expect("end marker must have a node parent");
        precedence
    }

    /// Given a node elem, return the first and last rec calls among it's components, it they exist.
    pub fn first_and_last_rec_calls(
        &self,
        node: GrammarElem,
    ) -> (Option<GrammarElem>, Option<GrammarElem>) {
        let rule_elem = self
            .first_parent(node)
            .expect("Node should have a rule parent");
        let rule = self.elem_data(rule_elem).as_non_terminal().unwrap();

        let mut rec_calls = self.childs(node).filter(|&elem| {
            matches!(self.elem_data(elem), GrammarNodeData::Proxy) && self.is_rec_call(rule, elem)
        });

        (rec_calls.next(), rec_calls.last())
    }

    fn is_rec_call(&self, rule: RuleId, proxy: GrammarElem) -> bool {
        let child = self.existing_first_child(proxy);

        let child_rule = self
            .elem_data(child)
            .as_non_terminal()
            .expect("Proxy should have a non-terminal child");

        match self.sibling_rules.get(&rule) {
            Some(siblings) => siblings.contains(&child_rule),
            None => false,
        }
    }

    pub fn rule_ends_with_assoc(
        &'_ self,
        rule: RuleId,
        expected_assoc: Associativity,
    ) -> impl '_ + Iterator<Item = GrammarElem> {
        self.sibling_rules
            .get(&rule)
            .unwrap()
            .into_iter()
            .flat_map(|rule| {
                let rule_elem = self.rule_elems.get(rule).unwrap();
                self.collect_end_markers(*rule_elem)
            })
            .filter(move |end_marker| {
                let node = self
                    .first_parent(*end_marker)
                    .expect("End marker should have a parent node");
                let (_, _, assoc) = self.elem_data(node).as_node().unwrap();
                assoc == Some(expected_assoc)
            })
    }

    fn collect_end_markers(&self, elem: GrammarElem) -> HashSet<GrammarElem> {
        let mut result = HashSet::new();

        let mut queue = OnceQueue::from([elem]);
        while let Some(elem_id) = queue.pop() {
            if self.elem_data(elem_id).is_end_marker() {
                result.insert(elem_id);
            } else {
                queue.extend(self.childs(elem_id));
            }
        }

        result
    }
}

impl Index<GrammarElem> for Grammar {
    type Output = GrammarNode;

    fn index(&self, index: GrammarElem) -> &Self::Output {
        self.graph.node_weight(index.0).unwrap()
    }
}

impl IndexMut<GrammarElem> for Grammar {
    fn index_mut(&mut self, index: GrammarElem) -> &mut Self::Output {
        self.graph.node_weight_mut(index.0).unwrap()
    }
}

pub struct GrammarBuilder<'s> {
    syntax: &'s Syntax,
    goal_rule: &'s str,
    grammar: Grammar,
}

impl<'s> GrammarBuilder<'s> {
    pub fn new(syntax: &'s Syntax, goal_rule: &'s str) -> Self {
        Self {
            syntax,
            goal_rule,
            grammar: Grammar {
                graph: Default::default(),
                sibling_rules: compute_rules_siblings(syntax),
                rule_elems: Default::default(),
                goal: Default::default(),
            },
        }
    }

    pub fn build(mut self) -> anyhow::Result<Grammar> {
        let goal_rule_id = self
            .syntax
            .get_rule_id(self.goal_rule)
            .ok_or_else(|| anyhow!("Invalid goal rule: {}", self.goal_rule))?;

        let root = self.insert_rule(goal_rule_id);

        self.grammar.goal = root;

        for alt in &self.syntax[goal_rule_id].alternatives.clone() {
            self.visit_rule_expr(root, alt);
        }

        let sets = GrammarSetsBuilder::new(&self.grammar).compute_sets();
        for (elem_id, (first, follow)) in sets {
            let elem = &mut self.grammar[elem_id];
            elem.first = first;
            elem.follow = follow;
        }

        Ok(self.grammar)
    }

    fn visit_rule(&mut self, rule_id: RuleId) -> GrammarElem {
        if let Some(elem) = self.grammar.rule_elems.get(&rule_id) {
            return *elem;
        }

        let rule_elem = self.insert_rule(rule_id);

        for alt in &self.syntax[rule_id].alternatives.clone() {
            self.visit_rule_expr(rule_elem, alt);
        }

        rule_elem
    }

    fn visit_rule_expr(&mut self, rule_elem: GrammarElem, rule_expr: &RuleExpr) -> GrammarElem {
        match rule_expr {
            RuleExpr::Ref(r) => {
                let rule_id = self.syntax.rule_id(&r.rule_name);
                self.create_proxy(rule_elem, rule_id)
            }
            RuleExpr::Node(n) => {
                let kind = self.syntax.existing_kind_id(&n.node_type);
                let node_elem =
                    self.insert_node(kind, n.precedence(), n.associativity(), rule_elem);
                let end_marker = self.insert_end_marker(node_elem);

                let mut comps = VecDeque::new();

                // petgraph orders the childs in their reverse insertion order, so we need to
                // insert them in reverse order.
                for comp in n.comps.iter().rev() {
                    let comp_elem = match comp {
                        AlternativeComp::Full(name, expr) => {
                            let elem = self.visit_comp_expr(node_elem, expr);
                            self.add_field(name, kind, elem);
                            elem
                        }
                        AlternativeComp::RuleRef(rule_name) => {
                            self.create_rule_proxy(node_elem, rule_name)
                        }
                        AlternativeComp::TExpr(t) => {
                            let tag_ids = match t {
                                TermExpr::Ref(term_name) => {
                                    let tag_id = self.syntax.tag_id(term_name);
                                    once(tag_id).collect()
                                }
                                TermExpr::Content(c) => {
                                    let tag_id = self.syntax.tag_id(c.as_str());
                                    once(tag_id).collect()
                                }
                                TermExpr::Alts(alts) => alts
                                    .iter()
                                    .map(|a| self.syntax.tag_id(a.as_str()))
                                    .collect(),
                            };

                            self.insert_term(tag_ids, node_elem)
                        }
                    };

                    comps.push_front(comp_elem);
                }

                for (&a, &b) in comps.iter().tuple_windows() {
                    self.add_sibling(a, b);
                }

                if let Some(&elem) = comps.back() {
                    self.add_sibling(elem, end_marker);
                }

                node_elem
            }
        }
    }

    fn visit_comp_expr(&mut self, parent: GrammarElem, expr: &CompExpr) -> GrammarElem {
        match expr {
            CompExpr::Ref(rule_name) => self.create_rule_proxy(parent, rule_name),
            CompExpr::Opt(rule_name) => {
                let elem = self.create_rule_proxy(parent, rule_name);
                self.make_optional(elem);
                elem
            }
            _ => unimplemented!(),
        }
    }

    fn create_rule_proxy(&mut self, parent: GrammarElem, rule_name: &str) -> GrammarElem {
        let rule_id = self.syntax.rule_id(rule_name);
        self.create_proxy(parent, rule_id)
    }

    fn add_field(&mut self, field_name: &str, kind: KindId, elem: GrammarElem) {
        let field_pos = self
            .syntax
            .field_position(kind, field_name)
            .unwrap_or_else(|| {
                let kind_name = &self.syntax[kind].name;
                panic!("Field '{field_name}' does not exist in node type {kind_name}")
            });

        self.grammar.index_mut(elem).field = Some(field_pos);
    }

    fn create_proxy(&mut self, parent: GrammarElem, rule: RuleId) -> GrammarElem {
        let rule_elem = self.visit_rule(rule);
        let proxy = self.insert_proxy(parent);
        self.add_child(proxy, rule_elem);
        proxy
    }

    fn insert_proxy(&mut self, parent: GrammarElem) -> GrammarElem {
        self.insert_node_data(GrammarNodeData::Proxy, parent)
    }

    fn insert_rule(&mut self, rule_id: RuleId) -> GrammarElem {
        let elem = self.add_node(GrammarNodeData::NonTerminal(rule_id));
        self.grammar.rule_elems.insert(rule_id, elem);
        elem
    }

    fn insert_end_marker(&mut self, parent: GrammarElem) -> GrammarElem {
        self.insert_node_data(GrammarNodeData::EndMarker, parent)
    }

    fn insert_node(
        &mut self,
        kind_id: KindId,
        precedence: Option<usize>,
        assoc: Option<Associativity>,
        parent: GrammarElem,
    ) -> GrammarElem {
        let id = self.insert_node_data(GrammarNodeData::Node(kind_id, precedence, assoc), parent);

        if id == parent {
            panic!("ha");
        }

        id
    }

    fn insert_term(&mut self, tag_ids: TagVec, parent: GrammarElem) -> GrammarElem {
        self.insert_node_data(GrammarNodeData::Terminal(tag_ids), parent)
    }

    fn insert_node_data(&mut self, data: GrammarNodeData, parent: GrammarElem) -> GrammarElem {
        let elem = self.add_node(data);
        self.add_child(parent, elem);
        elem
    }

    fn add_child(&mut self, parent: GrammarElem, child: GrammarElem) {
        self.add_edge(parent, child, GrammarEdge::Child);
    }

    fn add_sibling(&mut self, first: GrammarElem, second: GrammarElem) {
        self.add_edge(first, second, GrammarEdge::Sibling);
    }

    fn add_edge(&mut self, x: GrammarElem, y: GrammarElem, edge: GrammarEdge) {
        self.grammar.graph.add_edge(x.into(), y.into(), edge);
    }

    fn add_node(&mut self, node: GrammarNodeData) -> GrammarElem {
        self.grammar.graph.add_node(node.into()).into()
    }

    fn make_optional(&mut self, elem: GrammarElem) {
        self.grammar.index_mut(elem).optional = true;
    }
}

#[derive(Debug, Clone)]
struct GrammarSetsBuilder<'g> {
    first: HashMap<GrammarElem, HashSet<TagVec>>,
    seen_first: HashSet<GrammarElem>,
    follow: HashMap<GrammarElem, HashSet<TagVec>>,
    seen_follow: HashSet<GrammarElem>,
    grammar: &'g Grammar,
}

impl<'g> GrammarSetsBuilder<'g> {
    pub fn new(grammar: &'g Grammar) -> Self {
        GrammarSetsBuilder {
            grammar,
            follow: HashMap::new(),
            seen_follow: HashSet::new(),
            first: HashMap::new(),
            seen_first: HashSet::new(),
        }
    }

    pub fn compute_sets(mut self) -> HashMap<GrammarElem, (HashSet<TagVec>, HashSet<TagVec>)> {
        self.compute_firsts();
        self.compute_follows();

        // Because of the cyclical nature of the grammar, proxies can use memoized results
        // for the underlying rule before the rule sets are fully computed.
        // In order to mitigate that, we remove the proxy sets & recompute them with the
        // rule sets already fully computed during the previous run.
        // TODO: do the same for rules as well ?
        self.reset_seen();

        self.compute_firsts();
        self.compute_follows();

        self.first
            .into_iter()
            .map(|(elem, firsts)| (elem, (firsts, self.follow.remove(&elem).unwrap())))
            .collect()
    }

    fn reset_seen(&mut self) {
        self.seen_first.clear();
        self.seen_follow.clear();
    }

    fn compute_firsts(&mut self) {
        for elem in self.grammar.elems() {
            self.compute_first(elem, None);
        }
    }

    fn compute_first(&mut self, elem: GrammarElem, precedence: Option<usize>) -> HashSet<TagVec> {
        if self.seen_first.contains(&elem) {
            return self.first.get(&elem).cloned().unwrap_or_default();
        }
        self.seen_first.insert(elem);

        let mut result = match &self.grammar[elem].data {
            GrammarNodeData::EndMarker => HashSet::from([TagVec::new()]),
            GrammarNodeData::Terminal(tag_ids) => HashSet::from([tag_ids.clone()]),
            GrammarNodeData::Node(_, _, _) => {
                self.compute_first(self.grammar.existing_first_child(elem), precedence)
            }
            GrammarNodeData::NonTerminal(_) | GrammarNodeData::Proxy => {
                let childs: Vec<GrammarElem> = self.grammar.childs(elem).collect();
                self.compute_first_from(precedence, &childs)
            }
        };

        if result.contains(&TagVec::new()) || self.grammar[elem].optional {
            result.extend(self.compute_follow(elem));
        }

        self.first.insert(elem, result.clone());
        result
    }

    fn compute_first_from(
        &mut self,
        precedence: Option<usize>,
        childs_to_use: &[GrammarElem],
    ) -> HashSet<TagVec> {
        childs_to_use
            .iter()
            .flat_map(|&c| self.compute_first(c, precedence))
            .filter(|tags| !tags.is_empty())
            .collect()
    }

    fn compute_follows(&mut self) {
        for elem in self.grammar.elems() {
            self.compute_follow(elem);
        }
    }

    fn compute_follow(&mut self, elem: GrammarElem) -> HashSet<TagVec> {
        if self.seen_follow.contains(&elem) {
            return self.follow.get(&elem).cloned().unwrap_or_default();
        }
        self.seen_follow.insert(elem);

        let mut tags = HashSet::new();
        let mut include_parent_sibling = true;

        if let Some(sibling) = self.grammar.next_sibling(elem) {
            let first = self.compute_first(sibling, None);
            tags.extend(first);
            // If the element has a sibling, we do not want to include the parent's siblings first.
            include_parent_sibling = false;

            if self.grammar[sibling].optional {
                tags.extend(self.compute_follow(sibling))
            }
        }

        if include_parent_sibling {
            let parent_proxies: Vec<GrammarElem> = self.parent_rule_proxies(elem).collect();

            for p in parent_proxies {
                tags.extend(self.compute_follow(p).clone());
            }
        }

        self.follow.insert(elem, tags.clone());
        tags
    }

    fn parent_rule_proxies(
        &'_ self,
        element: GrammarElem,
    ) -> impl '_ + Iterator<Item = GrammarElem> {
        let mut current_elem = element;

        while !matches!(
            &self.grammar[current_elem].data,
            GrammarNodeData::NonTerminal(_)
        ) {
            if let Some(e) = self.grammar.first_parent(current_elem) {
                current_elem = e;
            } else {
                // Will be empty given the check above
                return self.grammar.parents(current_elem);
            }
        }

        self.grammar.parents(current_elem)
    }
}

fn compute_rules_siblings(syntax: &Syntax) -> HashMap<RuleId, NonEmpty<RuleId>> {
    syntax
        .rules_ids()
        .map(|id| (id, sibling_rules(syntax, id)))
        .collect()
}

fn sibling_rules(syntax: &Syntax, rule: RuleId) -> NonEmpty<RuleId> {
    let mut result = NonEmpty::new(rule);

    let mut siblings = find_new_siblings(syntax, &result);

    while !siblings.is_empty() {
        siblings.iter().for_each(|s| result.push(*s));
        siblings = find_new_siblings(syntax, &result);
    }

    result
}

fn find_new_siblings(syntax: &Syntax, rules: &NonEmpty<RuleId>) -> Vec<RuleId> {
    syntax
        .rules_ids()
        .filter(|&id| !rules.contains(&id) && rule_starts_with_call_to(syntax, rules, id))
        .collect()
}

fn rule_starts_with_call_to(syntax: &Syntax, targets: &NonEmpty<RuleId>, rule_id: RuleId) -> bool {
    let rule = &syntax[rule_id];

    let target_names: Vec<&str> = targets
        .iter()
        .map(|&t_id| syntax[t_id].name.as_str())
        .collect();

    let mut queue = OnceQueue::from(&rule.alternatives);
    while let Some(alt) = queue.pop() {
        match alt {
            RuleExpr::Ref(name) => {
                if target_names.contains(&name.rule_name.as_str()) {
                    return true;
                } else {
                    let subrule_id = syntax.rule_id(&name.rule_name);
                    queue.extend(&syntax[subrule_id].alternatives)
                }
            }
            RuleExpr::Node(n) => {
                let is_target_call = n
                    .comps
                    .first()
                    .map(|c| c.references_nonterm_in(&target_names))
                    .unwrap_or(false);

                if is_target_call {
                    return true;
                }
            }
        }
    }

    false
}

pub fn build_grammar(syntax: &Syntax, goal_rule: &str) -> anyhow::Result<Grammar> {
    GrammarBuilder::new(syntax, goal_rule).build()
}

#[cfg(test)]
pub mod test {
    use indoc::indoc;
    use itertools::Itertools;
    use maplit::hashset;

    use crate::core::spec::test::parse_spec;

    use super::*;

    #[test]
    #[ignore]
    fn scratch() {
        let spec = parse_spec(include_str!("../../test_res/specs/golang/golang.syl"));

        let grammar = build_grammar(&spec.syntax, "main").unwrap();

        let expected = indoc!("");

        assert_eq!(expected, render_grammar(&grammar, &spec.syntax));
    }

    #[test]
    fn rules_siblings() {
        let spec = parse_spec(indoc!(
            "
            node Plus { }
            node Expr { }
            node Num: Expr { }
            node Binop: Expr { 
                left: Expr,
                op: Plus, 
                right: Expr 
            }

            rule plus = Plus { `\\+` }

            rule main =
                plus_binop
              | Num { `[0-9]+` }

            rule plus_binop = [left] Binop { left@main op@plus right@main }  
        "
        ));

        let main_id = spec.syntax.rule_id("main");
        let plus_binop_id = spec.syntax.rule_id("plus_binop");

        let siblings = compute_rules_siblings(&spec.syntax);

        assert_eq!(
            hashset! { main_id, plus_binop_id},
            siblings
                .get(&plus_binop_id)
                .unwrap()
                .into_iter()
                .copied()
                .collect::<HashSet<RuleId>>()
        );
    }

    #[test]
    fn simple_list() {
        let spec = parse_spec(indoc!(
            "
            node A { field: List<B> }
            node B { }

            rule main = A { field@b_node+ }
            rule b_node = B { 'b' }
        "
        ));

        let grammar = build_grammar(&spec.syntax, "main").unwrap();

        let expected = indoc!(
            r#"
            0 - main:
            . A:
            . . 3 - some_b_node{ first = [<b>], follow = [<>] }
            . . ◌{ first = [<>], follow = [] }

            3 - some_b_node:
            . List:
            . . 3 - some_b_node{ first = [<b>], follow = [<b>] }
            . . 6 - b_node{ first = [<b>], follow = [<> | <b>] }
            . . ◌{ first = [<> | <b>], follow = [<> | <b>] }
            . List:
            . . 6 - b_node{ first = [<b>], follow = [<> | <b>] }
            . . ◌{ first = [<> | <b>], follow = [<> | <b>] }

            6 - b_node:
            . B:
            . . <b>{ first = [<b>], follow = [<> | <b>] }
            . . ◌{ first = [<> | <b>], follow = [<> | <b>] }"#
        );

        assert_eq!(expected, render_grammar(&grammar, &spec.syntax));
    }

    #[test]
    fn simple_left_rec() {
        let spec = parse_spec(indoc!(
            "
            node A { }

            rule main = A { main 'a' } | A { 'a' }
        "
        ));

        let grammar = build_grammar(&spec.syntax, "main").unwrap();

        let expected = indoc!(
            r#"
            0 - main:
            . A:
            . . <a>{ first = [<a>], follow = [<> | <a>] }
            . . ◌{ first = [<> | <a>], follow = [<a>] }
            . A:
            . . 0 - main{ first = [<a>], follow = [<a>] }
            . . <a>{ first = [<a>], follow = [<> | <a>] }
            . . ◌{ first = [<> | <a>], follow = [<a>] }"#
        );

        assert_eq!(expected, render_grammar(&grammar, &spec.syntax));
    }

    #[test]
    fn par_grammar_structure() {
        let spec = parse_spec(indoc!(
            "
            node Goal { }
            node List { }
            node Pair { }

            rule main = Goal { list }
            rule list = List { list pair  } | List { pair }
            rule pair = Pair { '(' ')' }
        "
        ));

        let grammar = build_grammar(&spec.syntax, "main").unwrap();

        let expected = indoc!(
            r#"
            0 - main:
            . Goal:
            . . 3 - list{ first = [<\(>], follow = [<>] }
            . . ◌{ first = [<>], follow = [] }

            3 - list:
            . List:
            . . 6 - pair{ first = [<\(>], follow = [<> | <\(>] }
            . . ◌{ first = [<> | <\(>], follow = [<> | <\(>] }
            . List:
            . . 3 - list{ first = [<\(>], follow = [<\(>] }
            . . 6 - pair{ first = [<\(>], follow = [<> | <\(>] }
            . . ◌{ first = [<> | <\(>], follow = [<> | <\(>] }

            6 - pair:
            . Pair:
            . . <\(>{ first = [<\(>], follow = [<\)>] }
            . . <\)>{ first = [<\)>], follow = [<> | <\(>] }
            . . ◌{ first = [<> | <\(>], follow = [<> | <\(>] }"#
        );

        assert_eq!(expected, render_grammar(&grammar, &spec.syntax));
    }

    #[test]
    fn first_and_follow() {
        let spec = parse_spec(indoc!(
            "\
                node Par { }
    
                term L_PAR = '('
                term R_PAR = ')'
    
                rule main = Par { L_PAR R_PAR }
            "
        ));

        let grammar = build_grammar(&spec.syntax, "main").unwrap();

        let l_par_tag = spec.syntax.tag_id("L_PAR");
        let goal_first = &grammar[grammar.goal].first;

        assert_eq!(goal_first, &HashSet::from([TagVec::from(vec![l_par_tag])]));
    }

    pub fn render_grammar(grammar: &Grammar, syntax: &Syntax) -> String {
        grammar
            .graph
            .node_indices()
            .filter_map(|elem| match &grammar[elem.into()].data {
                GrammarNodeData::NonTerminal(rule_id) => {
                    Some(render_rule(syntax, grammar, elem.into(), *rule_id))
                }
                _ => None,
            })
            .join("\n\n")
    }

    fn render_rule(
        syntax: &Syntax,
        grammar: &Grammar,
        elem: GrammarElem,
        rule_id: RuleId,
    ) -> String {
        let rule_name = render_rule_name(syntax, elem, rule_id);

        let childs = grammar
            .childs(elem)
            .map(|e| render_grammar_element(syntax, grammar, 1, e))
            .join("\n");

        format!("{rule_name}:\n{childs}")
    }

    fn render_grammar_element(
        syntax: &Syntax,
        grammar: &Grammar,
        indentation: usize,
        elem_id: GrammarElem,
    ) -> String {
        let indent = ". ".repeat(indentation);

        let elem = &grammar[elem_id];

        let first_and_follow = if matches!(
            &elem.data,
            GrammarNodeData::Proxy | GrammarNodeData::EndMarker | GrammarNodeData::Terminal(_)
        ) {
            render_fist_and_follow(syntax, elem)
        } else {
            String::new()
        };

        let repr = match &elem.data {
            GrammarNodeData::NonTerminal(rule_id) => render_rule_name(syntax, elem_id, *rule_id),
            GrammarNodeData::Proxy => {
                let child = grammar.existing_first_child(elem_id);
                if let &GrammarNodeData::NonTerminal(rule_id) = &grammar[child].data {
                    render_rule_name(syntax, child, rule_id)
                } else {
                    panic!("proxy child is not a non-terminal")
                }
            }
            GrammarNodeData::Node(kind_id, _, _) => syntax.kind_name(*kind_id).to_string(),
            GrammarNodeData::Terminal(tags) => render_tag_vec(syntax, tags),
            GrammarNodeData::EndMarker => "◌".to_string(),
        };

        let childs_repr = if let GrammarNodeData::Node(_, _, _) = &elem.data {
            ":\n".to_string()
                + &grammar
                    .childs(elem_id)
                    .map(|e| render_grammar_element(syntax, grammar, indentation + 1, e))
                    .join("\n")
        } else {
            String::new()
        };

        format!("{indent}{repr}{first_and_follow}{childs_repr}")
    }

    fn render_fist_and_follow(syntax: &Syntax, elem: &GrammarNode) -> String {
        let first = render_tagvec_set(syntax, &elem.first);
        let follow = render_tagvec_set(syntax, &elem.follow);

        format!("{{ first = {first}, follow = {follow} }}")
    }

    fn render_tagvec_set(syntax: &Syntax, tags: &HashSet<TagVec>) -> String {
        let tagvecs_repr = tags
            .iter()
            .map(|t| render_tag_vec(syntax, t))
            .sorted()
            .join(" | ");
        format!("[{tagvecs_repr}]")
    }

    fn render_tag_vec(syntax: &Syntax, tags: &TagVec) -> String {
        let tags_repr = tags.iter().map(|t| syntax.tag_name(*t)).join(",");
        format!("<{tags_repr}>")
    }

    fn render_rule_name(syntax: &Syntax, elem: GrammarElem, rule: RuleId) -> String {
        format!("{} - {}", elem.0.index(), &syntax[rule].name)
    }
}
