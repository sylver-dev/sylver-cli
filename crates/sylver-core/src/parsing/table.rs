use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use derive_more::{From, Into};
use itertools::Itertools;
use rustc_hash::FxHashSet;

use sylver_dsl::meta::*;

use crate::{
    core::spec::{FieldPos, KindId, RuleId, Syntax, TagId, TagVec},
    parsing::grammar::{build_grammar, Grammar, GrammarElem, GrammarNodeData},
    util::{
        debug::render_table,
        once::{OnceQueue, UniqueSmallVec},
    },
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, From, Into)]
pub struct ParsingState(usize);

impl ParsingState {
    pub const fn from_index(index: usize) -> ParsingState {
        ParsingState(index)
    }

    pub const fn index(&self) -> usize {
        self.0
    }
}

pub type GotoEntries = UniqueSmallVec<GotoEntry>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GotoEntry {
    pub state: ParsingState,
    pub field: Option<FieldPos>,
    pub forbidden: FxHashSet<GrammarElem>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ParsingAction {
    Shift(ParsingState),
    Empty(ParsingState),
    Reduce(RuleId, KindId, usize, GrammarElem),
    Accept(RuleId, KindId, usize),
}

pub type ParsingActions = UniqueSmallVec<ParsingAction>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsingTable {
    pub actions: Vec<BTreeMap<Option<TagId>, ParsingActions>>,
    pub goto: Vec<BTreeMap<RuleId, GotoEntries>>,
}

impl ParsingTable {
    pub fn render(&self, syntax: &Syntax) -> String {
        let actions = self.render_actions_table(syntax);
        let gotos = self.render_goto_table(syntax);
        format!("ACTIONS:\n{actions}\n\nGOTOS:\n{gotos}")
    }

    fn render_actions_table(&self, syntax: &Syntax) -> String {
        let terminals: Vec<Option<TagId>> = self
            .actions
            .iter()
            .flat_map(|m| m.keys())
            .cloned()
            .sorted()
            .dedup()
            .collect();

        let mut terminal_reprs: Vec<String> = terminals
            .iter()
            .map(|opt_t| opt_t.map(|t| syntax[t].name.clone()).unwrap_or_default())
            .collect();

        terminal_reprs.insert(0, "State".into());

        let content: Vec<Vec<String>> = (0..self.actions.len())
            .map(|i| {
                let mut terms = terminals
                    .iter()
                    .map(|t| {
                        self.render_actions(
                            syntax,
                            &self.actions[i].get(t).cloned().unwrap_or_default(),
                        )
                    })
                    .collect::<Vec<_>>();

                terms.insert(0, i.to_string());

                terms
            })
            .collect();

        render_table(&terminal_reprs, content)
    }

    fn render_actions(&self, syntax: &Syntax, actions: &UniqueSmallVec<ParsingAction>) -> String {
        actions
            .iter()
            .map(|a| self.render_action(syntax, a))
            .join(", ")
    }

    fn render_action(&self, syntax: &Syntax, action: &ParsingAction) -> String {
        match action {
            ParsingAction::Empty(s) => format!("𝜀({})", s.0),
            ParsingAction::Shift(s) => format!("s({})", s.0),
            ParsingAction::Reduce(rule, kind, arity, _) => format!(
                "r({}, {}, {})",
                &syntax[*rule].name, &syntax[*kind].name, arity
            ),
            ParsingAction::Accept(rule, kind, arity) => format!(
                "a({}, {}, {})",
                &syntax[*rule].name, &syntax[*kind].name, arity
            ),
        }
    }

    fn render_goto_table(&self, syntax: &Syntax) -> String {
        let rules: Vec<RuleId> = self
            .goto
            .iter()
            .flat_map(|m| m.keys())
            .cloned()
            .sorted()
            .dedup()
            .collect();

        let mut rules_repr: Vec<String> = rules.iter().map(|&id| syntax[id].name.clone()).collect();
        rules_repr.insert(0, "State".into());

        let content: Vec<Vec<String>> = (0..self.goto.len())
            .map(|i| {
                let mut entries: Vec<String> = rules
                    .iter()
                    .map(|id| {
                        self.goto[i]
                            .get(id)
                            .map(|entries| self.render_entries(entries))
                            .unwrap_or_default()
                    })
                    .collect();

                if entries.iter().any(|s| !s.is_empty()) {
                    entries.insert(0, i.to_string());
                }

                entries
            })
            .filter(|line| line.iter().any(|x| !x.is_empty()))
            .collect();

        render_table(&rules_repr, content)
    }

    fn render_entries(&self, entries: &GotoEntries) -> String {
        entries.iter().map(|e| e.state.0.to_string()).join(", ")
    }
}

pub fn build_table(syntax: &Syntax, goal_rule: &str) -> anyhow::Result<ParsingTable> {
    let grammar = build_grammar(syntax, goal_rule)?;
    TableBuilder::new(grammar).build()
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct LRItem {
    placeholder: GrammarElem,
}

impl LRItem {
    fn advance(&self, grammar: &Grammar) -> Option<LRItem> {
        grammar
            .next_sibling(self.placeholder)
            .map(|placeholder| LRItem { placeholder })
    }
}

// TODO: since ParsingState is a usize, and every state has matching transitions, why not use a vec ?
type StatesTransitions = HashMap<ParsingState, HashSet<(Transition, ParsingState)>>;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum TransitionData {
    Terminal(TagVec),
    Rule {
        rule_elem: GrammarElem,
        field: Option<FieldPos>,
        proxy_elem: GrammarElem,
    },
    Epsilon(GrammarElem),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct Transition {
    data: TransitionData,
    optional: bool,
}

struct TableBuilder {
    table: ParsingTable,
    grammar: Grammar,
    final_rules: HashSet<RuleId>,
}

impl TableBuilder {
    pub fn new(grammar: Grammar) -> Self {
        TableBuilder {
            table: ParsingTable {
                actions: vec![],
                goto: vec![],
            },
            final_rules: TableBuilder::final_rules(&grammar),
            grammar,
        }
    }

    fn final_rules(grammar: &Grammar) -> HashSet<RuleId> {
        let mut result = HashSet::new();

        let mut queue = OnceQueue::from([grammar.goal]);
        while let Some(elem) = queue.pop() {
            match grammar.elem_data(elem) {
                GrammarNodeData::NonTerminal(rule_id) => {
                    result.insert(*rule_id);
                    queue.extend(grammar.childs(elem));
                }
                GrammarNodeData::Proxy => queue.extend(grammar.childs(elem)),
                _ => (),
            }
        }

        result
    }

    fn build(mut self) -> anyhow::Result<ParsingTable> {
        let (states, transitions) = build_canonical_set(&self.grammar);

        self.table.actions = vec![BTreeMap::new(); states.len()];
        self.table.goto = vec![BTreeMap::new(); states.len()];

        let end_markers_prec = self.grammar.end_markers_with_precedence();
        for (set_id, transitions) in transitions.into_iter() {
            self.process_set(set_id, &states[set_id.0], &transitions, &end_markers_prec);
        }

        Ok(self.table)
    }

    fn process_set(
        &mut self,
        state: ParsingState,
        set: &BTreeSet<LRItem>,
        transitions: &HashSet<(Transition, ParsingState)>,
        end_markers_prec: &HashMap<usize, FxHashSet<GrammarElem>>,
    ) {
        for item in set {
            let grammar_elem = &self.grammar[item.placeholder];

            if grammar_elem.data == GrammarNodeData::EndMarker {
                let set_actions = &mut self.table.actions[state.0];

                let (node_elem, node_kind) = end_marker_kind(&self.grammar, item.placeholder);
                let rule_id = node_rule(&self.grammar, node_elem);

                // The end marker doesn't increase the arity;
                let arity = self.grammar.childs(node_elem).count() - 1;

                if self.final_rules.contains(&rule_id) {
                    set_actions
                        .entry(None)
                        .or_default()
                        .push(ParsingAction::Accept(rule_id, node_kind, arity));
                }

                let action = ParsingAction::Reduce(rule_id, node_kind, arity, item.placeholder);

                for lookahead in &self.grammar[item.placeholder].follow {
                    if lookahead.is_empty() {
                        set_actions.entry(None).or_default().push(action);
                    } else {
                        for &tag in lookahead {
                            set_actions.entry(Some(tag)).or_default().push(action);
                        }
                    }
                }
            }
        }

        for (transition_elem, target_state) in transitions.iter() {
            match &transition_elem.data {
                TransitionData::Terminal(tags) => {
                    self.add_shift(state, tags, *target_state);
                }
                TransitionData::Rule {
                    rule_elem,
                    field,
                    proxy_elem,
                } => {
                    let node_elem = self
                        .grammar
                        .first_parent(*proxy_elem)
                        .expect("Proxy should have a node parent");

                    let (_, prec, assoc) = self.grammar.elem_data(node_elem).as_node().unwrap();

                    let assoc_forbidden = match self.grammar.first_and_last_rec_calls(node_elem) {
                        (Some(first), Some(last)) => {
                            let rule = self
                                .grammar
                                .elem_data(*rule_elem)
                                .as_non_terminal()
                                .unwrap();
                            if let Some(assoc) = assoc {
                                if (assoc == Associativity::Left && *proxy_elem == last)
                                    || (assoc == Associativity::Right && *proxy_elem == first)
                                {
                                    self.grammar
                                        .rule_ends_with_assoc(rule, assoc)
                                        .filter(|&end_marker| {
                                            match (
                                                self.grammar.node_child_precedence(end_marker),
                                                prec,
                                            ) {
                                                (Some(elem_prec), Some(p)) => elem_prec <= p,
                                                _ => true,
                                            }
                                        })
                                        .collect()
                                } else {
                                    FxHashSet::default()
                                }
                            } else {
                                FxHashSet::default()
                            }
                        }
                        _ => FxHashSet::default(),
                    };

                    let mut forbidden = match prec {
                        None => FxHashSet::default(),
                        Some(p) => end_markers_prec
                            .iter()
                            .filter(|(&item_p, _)| item_p < p)
                            .flat_map(|(_, elems)| elems)
                            .copied()
                            .collect(),
                    };

                    forbidden.extend(assoc_forbidden);

                    for rule_id in self.expand_rule_elem(*rule_elem) {
                        self.table.goto[state.0]
                            .entry(rule_id)
                            .or_default()
                            .push(GotoEntry {
                                field: *field,
                                state: *target_state,
                                forbidden: forbidden.clone(),
                            })
                    }
                }
                TransitionData::Epsilon(elem_id) => {
                    let elem = &self.grammar[*elem_id];

                    if elem.first.is_empty() {
                        self.table.actions[state.0]
                            .entry(None)
                            .or_default()
                            .push(ParsingAction::Empty(*target_state));
                    }

                    for tags in elem.first.clone() {
                        self.add_empty(state, &tags, *target_state);
                    }
                }
            }
        }
    }

    fn add_shift(&mut self, source_state: ParsingState, tags: &TagVec, target_state: ParsingState) {
        for &tag in tags {
            self.table.actions[source_state.0]
                .entry(Some(tag))
                .or_default()
                .push(ParsingAction::Shift(target_state));
        }
    }

    fn expand_rule_elem(&self, elem: GrammarElem) -> Vec<RuleId> {
        let mut result = vec![];
        let mut queue = OnceQueue::from([elem]);

        while let Some(current_elem) = queue.pop() {
            match self.grammar.elem_data(current_elem) {
                GrammarNodeData::NonTerminal(rule_id) => {
                    result.push(*rule_id);
                    queue.extend(self.grammar.childs(current_elem));
                }
                GrammarNodeData::Proxy => {
                    queue.extend(self.grammar.childs(current_elem));
                }
                _ => {}
            }
        }

        result
    }

    fn add_empty(&mut self, source_state: ParsingState, tags: &TagVec, target_state: ParsingState) {
        if tags.is_empty() {
            self.table.actions[source_state.0]
                .entry(None)
                .or_default()
                .push(ParsingAction::Empty(target_state));
        } else {
            for &tag in tags {
                self.table.actions[source_state.0]
                    .entry(Some(tag))
                    .or_default()
                    .push(ParsingAction::Empty(target_state));
            }
        }
    }
}

fn end_marker_kind(grammar: &Grammar, end_marker: GrammarElem) -> (GrammarElem, KindId) {
    grammar
        .parents(end_marker)
        .filter_map(|parent_id| {
            grammar[parent_id]
                .data
                .as_node()
                .map(|(kind, _, _)| (parent_id, kind))
        })
        .next()
        .expect("end marker must have a node parent")
}

fn node_rule(grammar: &Grammar, node: GrammarElem) -> RuleId {
    grammar
        .parents(node)
        .filter_map(|parent_id| grammar[parent_id].data.as_non_terminal())
        .next()
        .expect("node must have a non-terminal parent")
}

fn build_canonical_set(grammar: &Grammar) -> (Vec<BTreeSet<LRItem>>, StatesTransitions) {
    let mut set_ids = HashMap::new();
    let mut transitions = HashMap::new();
    let mut queue = OnceQueue::new();

    let mut global_cache = HashMap::new();
    let mut local_cache = HashMap::new();

    let init_set = closure(
        &mut global_cache,
        &mut local_cache,
        grammar,
        &root_items(grammar),
    );
    let init_set_id = ParsingState(0);

    queue.push((init_set_id, init_set.clone()));
    set_ids.insert(init_set, init_set_id);

    while let Some((set_id, set)) = queue.pop() {
        let set_transitions: &mut HashSet<(Transition, ParsingState)> =
            transitions.entry(set_id).or_default();

        for (elem, next_set) in goto(grammar, &mut global_cache, &mut local_cache, &set) {
            let next_set_id = match set_ids.get(&next_set) {
                Some(id) => *id,
                None => {
                    let id = ParsingState(set_ids.len());

                    queue.push((id, next_set.clone()));
                    set_ids.insert(next_set.clone(), id);

                    id
                }
            };

            set_transitions.insert((elem, next_set_id));
        }
    }

    for (lr_items, state_id) in set_ids.iter() {
        let set_transitions = transitions.entry(*state_id).or_default();

        for lr_item in lr_items {
            let placeholder = &grammar[lr_item.placeholder];
            if placeholder.optional {
                if let Some(following_elem) = grammar.next_sibling(lr_item.placeholder) {
                    let target_sets = set_ids
                        .iter()
                        .filter(|(items, _)| {
                            items.iter().any(|item| item.placeholder == following_elem)
                        })
                        .map(|(_, id)| id);

                    for &set in target_sets {
                        set_transitions.insert((
                            Transition {
                                data: TransitionData::Epsilon(following_elem),
                                optional: false,
                            },
                            set,
                        ));
                    }
                }
            }
        }
    }

    let sets_vec = set_ids
        .into_iter()
        .sorted_by_key(|(_, id)| *id)
        .map(|(set, _)| set)
        .collect();

    (sets_vec, transitions)
}

fn goto(
    grammar: &Grammar,
    cache: &mut HashMap<BTreeSet<LRItem>, BTreeSet<LRItem>>,
    new_cache: &mut HashMap<LRItem, BTreeSet<LRItem>>,
    set: &BTreeSet<LRItem>,
) -> HashMap<Transition, BTreeSet<LRItem>> {
    let mut result: HashMap<Transition, BTreeSet<LRItem>> = HashMap::new();

    for item in set {
        if let Some(next_item) = item.advance(grammar) {
            let placeholder = &grammar[item.placeholder];
            let transition_data = match &placeholder.data {
                GrammarNodeData::Terminal(tags) => Some(TransitionData::Terminal(tags.clone())),
                GrammarNodeData::Proxy => {
                    let rule_elem = grammar.existing_first_child(item.placeholder);
                    Some(TransitionData::Rule {
                        rule_elem,
                        field: placeholder.field,
                        proxy_elem: item.placeholder,
                    })
                }
                _ => None,
            };

            if let Some(tr) = transition_data {
                let transition = Transition {
                    optional: placeholder.optional,
                    data: tr,
                };

                result.entry(transition).or_default().insert(next_item);
            }
        }
    }

    result.values_mut().for_each(|s| {
        *s = closure(cache, new_cache, grammar, s);
    });

    result
}

fn closure(
    global_cache: &mut HashMap<BTreeSet<LRItem>, BTreeSet<LRItem>>,
    local_cache: &mut HashMap<LRItem, BTreeSet<LRItem>>,
    grammar: &Grammar,
    set: &BTreeSet<LRItem>,
) -> BTreeSet<LRItem> {
    if global_cache.contains_key(set) {
        return global_cache.get(set).unwrap().clone();
    }

    let mut updated = set.clone();
    let mut to_visit = VecDeque::from_iter(set.iter().cloned());

    while let Some(item) = to_visit.pop_front() {
        for new_item in item_closure(grammar, local_cache, item) {
            if !updated.contains(&new_item) {
                to_visit.push_back(new_item);
                updated.insert(new_item);
            }
        }
    }

    global_cache.insert(set.clone(), updated.clone());

    updated
}

fn item_closure(
    grammar: &Grammar,
    cache: &mut HashMap<LRItem, BTreeSet<LRItem>>,
    item: LRItem,
) -> BTreeSet<LRItem> {
    if let Some(cl) = cache.get(&item) {
        return cl.clone();
    }

    cache.insert(item, BTreeSet::default());

    match grammar.elem_data(item.placeholder) {
        GrammarNodeData::NonTerminal(_) | GrammarNodeData::Proxy => {
            for child in grammar.childs(item.placeholder) {
                let child_item = LRItem { placeholder: child };
                let child_closure = item_closure(grammar, cache, child_item);

                let item_entry = cache.entry(item).or_default();
                item_entry.insert(child_item);
                item_entry.extend(child_closure);
            }
        }
        GrammarNodeData::Node(_, _, _) => {
            let first_child = grammar.existing_first_child(item.placeholder);
            let first_child_item = LRItem {
                placeholder: first_child,
            };
            let first_child_closure = item_closure(grammar, cache, first_child_item);
            let item_entry = cache.entry(item).or_default();
            item_entry.insert(first_child_item);
            item_entry.extend(first_child_closure);
        }
        GrammarNodeData::EndMarker => {}
        GrammarNodeData::Terminal(_) => {}
    }

    cache.entry(item).or_default().clone()
}

fn root_items(grammar: &Grammar) -> BTreeSet<LRItem> {
    let mut result = BTreeSet::new();

    let mut queue = OnceQueue::from([grammar.goal]);

    while let Some(elem) = queue.pop() {
        match &grammar[elem].data {
            GrammarNodeData::Node(_, _, _) => {
                result.insert(LRItem {
                    placeholder: grammar.existing_first_child(elem),
                });
            }
            GrammarNodeData::NonTerminal(_) | GrammarNodeData::Proxy => {
                queue.extend(grammar.childs(elem));
            }
            d @ (GrammarNodeData::Terminal(_) | GrammarNodeData::EndMarker) => {
                panic!("Elem {d:?} should not be the child of the root grammar element.")
            }
        }
    }

    result
}

#[cfg(test)]
mod test {
    use indoc::indoc;

    use crate::{
        core::spec::test::parse_spec,
        parsing::grammar::{build_grammar, test::render_grammar},
    };

    use super::*;

    #[test]
    fn root_items_ok() {
        let spec = indoc!(
            "
            node Goal { }
            node List { }
            node Pair { }

            term LPAR = '('
            term RPAR = ')' 

            rule main = Goal { list }
            rule list = List { list pair  } | List { pair }
            rule pair = Pair { LPAR pair RPAR } | Pair { LPAR RPAR }
        "
        );

        let syntax = parse_spec(spec).syntax;

        let grammar = build_grammar(&syntax, "main").unwrap();

        render_grammar(&grammar, &syntax);

        let root_set = root_items(&grammar);
        println!("{}", render_set(&root_set));

        let mut global_cache = HashMap::new();
        let mut local_cache = HashMap::new();
        let root_closure = closure(&mut global_cache, &mut local_cache, &grammar, &root_set);
        println!("{}", render_set(&root_closure));

        goto(&grammar, &mut global_cache, &mut local_cache, &root_closure);

        build_canonical_set(&grammar).0.len();
    }

    fn render_lr_item(item: &LRItem) -> String {
        format!("[{}]", item.placeholder.index())
    }

    fn render_set(set: &BTreeSet<LRItem>) -> String {
        let items_repr = set
            .iter()
            .map(render_lr_item)
            .collect::<Vec<_>>()
            .join(", ");

        format!("[{items_repr}]")
    }
}
