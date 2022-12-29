use std::{
    cmp::Ordering,
    collections::{HashSet, VecDeque},
    ops::{Index, IndexMut},
    path::PathBuf,
};

use derive_more::{From, Into};
use itertools::Itertools;
use maplit::hashset;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{smallvec, SmallVec};
use thiserror::Error;

use crate::{
    core::{
        pos::{InclPosRange, Pos},
        spec::{KindId, RuleId, Syntax, TagId, COMMENT_NODE_KIND},
    },
    parsing::{
        grammar::GrammarElem,
        scanner::{Scanner, Token, TokenRes},
        sppf::{PackedParseForest, TreeNodeId},
        table::{ParsingAction, ParsingState, ParsingTable},
    },
    report::{Report, ReportKind},
    util::once::UniqueSmallVec,
};

static INIT_STATE: ParsingState = ParsingState::from_index(0);

type SmallArrayVec<T, const N: usize = 6> = SmallVec<[T; N]>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, From, Into)]
struct StackPos(usize);

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct StackEntry {
    state: ParsingState,
    node: Option<TreeNodeId>,
    ignore_node: Option<TreeNodeId>,
    pos: Pos,
}

impl StackEntry {
    fn from_state(pos: Pos, state: ParsingState) -> StackEntry {
        StackEntry {
            state,
            node: None,
            ignore_node: None,
            pos,
        }
    }

    fn new(pos: Pos, state: ParsingState, node: TreeNodeId) -> StackEntry {
        StackEntry {
            state,
            node: Some(node),
            ignore_node: None,
            pos,
        }
    }
}

struct GLRStack {
    nodes: Vec<StackEntry>,
    predecessors: FxHashMap<StackPos, FxHashSet<StackPos>>,
    successors: FxHashMap<StackPos, FxHashSet<StackPos>>,
    tops: VecDeque<Vec<StackPos>>,
}

impl GLRStack {
    pub fn new(state: ParsingState) -> GLRStack {
        GLRStack {
            nodes: vec![StackEntry::from_state(Pos::default(), state)],
            predecessors: FxHashMap::default(),
            successors: FxHashMap::default(),
            tops: VecDeque::from([vec![StackPos(0)]]),
        }
    }

    fn push_entry(&mut self, current_pos: StackPos, entry: StackEntry) -> StackPos {
        let existing_entry = self
            .find_existing_in_tops(entry)
            .or_else(|| self.find_existing_in_successors(current_pos, entry));

        let new_pos = if let Some(entry_pos) = existing_entry {
            self.set_successor(current_pos, entry_pos);
            entry_pos
        } else {
            self.create_successor(current_pos, entry)
        };

        self.remove_from_tops(current_pos);
        self.add_to_top(entry.pos, new_pos);

        new_pos
    }

    fn smallest_top_pos(&self) -> Option<usize> {
        self.tops.get(0).map(|es| self[es[0]].pos.txt_pos)
    }

    fn take_tops(&mut self) -> Vec<StackPos> {
        self.tops.pop_front().unwrap_or_default()
    }

    fn find_existing_in_tops(&self, entry: StackEntry) -> Option<StackPos> {
        self.tops
            .iter()
            .find(|es| self[es[0]].pos == entry.pos)
            .and_then(|same_pos_entries| same_pos_entries.iter().find(|&&e| self[e] == entry))
            .copied()
    }

    fn find_existing_in_successors(&self, pos: StackPos, entry: StackEntry) -> Option<StackPos> {
        self.successors
            .get(&pos)
            .into_iter()
            .flatten()
            .find(|&&e| self[e] == entry)
            .copied()
    }

    pub fn discard(&mut self, top: StackPos) {
        self.remove_from_tops(top);
    }

    pub fn remove_and_get_preds(&mut self, top: StackPos) -> SmallVec<[StackPos; 3]> {
        self.remove_from_tops(top);

        let res: SmallVec<[StackPos; 3]> = self.predecessors(top).into_iter().collect();

        res
    }

    fn remove_from_tops(&mut self, pos: StackPos) {
        let buff_id = self
            .tops
            .iter()
            .position(|es| self[es[0]].pos.txt_pos == self[pos].pos.txt_pos);

        if let Some(buff_id) = buff_id {
            let buff = &mut self.tops[buff_id];
            if let Some(id) = buff.iter().position(|p| *p == pos) {
                buff.remove(id);
                if buff.is_empty() {
                    self.tops.remove(buff_id);
                }
            }
        }
    }

    fn add_to_top(&mut self, input_pos: Pos, pos: StackPos) {
        for i in 0..self.tops.len() {
            match self[self.tops[i][0]].pos.txt_pos.cmp(&input_pos.txt_pos) {
                Ordering::Equal if !self.tops[i].iter().any(|e| self[*e] == self[pos]) => {
                    self.tops[i].push(pos);
                    return;
                }
                Ordering::Greater => {
                    self.tops.insert(i, vec![pos]);
                    return;
                }
                _ => (),
            }
        }

        self.tops.push_back(vec![pos]);
    }

    fn create_successor(&mut self, pos: StackPos, entry: StackEntry) -> StackPos {
        let new_id = self.add_entry(entry);
        self.set_successor(pos, new_id);
        new_id
    }

    fn add_entry(&mut self, entry: StackEntry) -> StackPos {
        let index = self.nodes.len();
        self.nodes.push(entry);
        index.into()
    }

    fn set_successor(&mut self, predecessor: StackPos, successor: StackPos) {
        self.successors
            .entry(predecessor)
            .or_default()
            .insert(successor);

        self.predecessors
            .entry(successor)
            .or_default()
            .insert(predecessor);
    }

    fn predecessors(&self, pos: StackPos) -> SmallVec<[StackPos; 3]> {
        self.predecessors
            .get(&pos)
            .map(|ids| ids.iter().copied().collect())
            .unwrap_or_default()
    }
}

impl Index<StackPos> for GLRStack {
    type Output = StackEntry;

    fn index(&self, index: StackPos) -> &Self::Output {
        &self.nodes[index.0]
    }
}

impl IndexMut<StackPos> for GLRStack {
    fn index_mut(&mut self, index: StackPos) -> &mut Self::Output {
        &mut self.nodes[index.0]
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Error)]
pub enum ParserError {
    #[error("Unexpected token")]
    UnexpectedToken(Pos, ParsingState),
    #[error("Unexpected end of file")]
    UnexpectedEof(Pos, ParsingState),
}

impl ParserError {
    /// Create a `Report` from the current parser error.
    pub fn to_reports(
        &self,
        parser: &Parser,
        file_path: impl Clone + Into<PathBuf>,
    ) -> Vec<Report> {
        match self {
            ParserError::UnexpectedEof(pos, state) => {
                vec![Self::unexpected_eof_report(file_path, parser, *pos, *state)]
            }
            ParserError::UnexpectedToken(pos, state) => {
                Self::unexpected_token_reports(file_path, parser, *pos, *state)
            }
        }
    }

    fn unexpected_eof_report(
        path: impl Into<PathBuf>,
        parser: &Parser,
        pos: Pos,
        state: ParsingState,
    ) -> Report {
        Report {
            file_path: path.into(),
            kind: ReportKind::Error,
            code: "unexpected_eof".to_string(),
            message: format!(
                "Unexpected EOF, expected: {}",
                Self::expected_tag_names(parser, state).join(", ")
            ),
            position: InclPosRange::new(pos, pos).unwrap(),
            note: None,
        }
    }

    fn unexpected_token_reports(
        path: impl Clone + Into<PathBuf>,
        parser: &Parser,
        pos: Pos,
        state: ParsingState,
    ) -> Vec<Report> {
        let expected_tags = Self::expected_tags(parser, state);

        Self::matched_tokens(parser, &expected_tags, pos)
            .into_iter()
            .map(|t| Report {
                file_path: path.clone().into(),
                kind: ReportKind::Error,
                code: "unexpected_token".to_string(),
                message: format!(
                    "Unexpected {}, expected: {}",
                    parser.syntax.tag_name(t.token.tag),
                    tag_names(parser.syntax, &expected_tags).join(", ")
                ),
                position: InclPosRange::new(pos, t.updated_pos).unwrap(),
                note: None,
            })
            .collect()
    }

    fn matched_tokens(parser: &Parser, expected_tags: &[TagId], pos: Pos) -> Vec<TokenRes> {
        let expected_matches =
            parser
                .scanner
                .tokens_for_tags(parser.input_str, pos, expected_tags.iter().copied());

        if !expected_matches.is_empty() {
            return expected_matches.to_vec();
        }

        let all_tags = parser.syntax.terminals().map(|(tag, _)| tag);

        parser
            .scanner
            .tokens_for_tags(parser.input_str, pos, all_tags)
            .to_vec()
    }

    fn expected_tag_names(parser: &Parser, state: ParsingState) -> Vec<String> {
        tag_names(parser.syntax, &Self::expected_tags(parser, state)).collect()
    }

    fn expected_tags(parser: &Parser, state: ParsingState) -> Vec<TagId> {
        parser.table.actions[state.index()]
            .keys()
            .filter_map(|k| *k)
            .collect()
    }
}

fn tag_names<'s>(syntax: &'s Syntax, tags: &'s [TagId]) -> impl 's + Iterator<Item = String> {
    tags.iter().map(|&t| syntax.tag_name(t).to_string())
}

pub struct Parser<'t> {
    stack: GLRStack,
    pub tree: PackedParseForest,
    accepted: bool,
    errors: FxHashMap<usize, UniqueSmallVec<ParserError>>,
    table: &'t ParsingTable,
    syntax: &'t Syntax,
    scanner: &'t Scanner,
    input_str: &'t str,
}

impl<'t> Parser<'t> {
    pub fn new(
        syntax: &'t Syntax,
        table: &'t ParsingTable,
        scanner: &'t Scanner,
        input_str: &'t str,
    ) -> Self {
        Parser {
            stack: GLRStack::new(INIT_STATE),
            tree: PackedParseForest::new(),
            errors: FxHashMap::default(),
            accepted: false,
            syntax,
            table,
            scanner,
            input_str,
        }
    }

    pub fn parse(&mut self) {
        while self
            .stack
            .smallest_top_pos()
            .map(|p| p <= self.input_str.len())
            .unwrap_or(false)
        {
            self.process_tops();
        }
    }

    pub fn collect_errors(&mut self) -> HashSet<ParserError> {
        let last_pos = self
            .tree
            .nodes()
            .map(|n| n.span.most_advanced_pos())
            .max()
            .unwrap_or_default();

        if last_pos == self.input_str.len() {
            return hashset![];
        }

        self.errors
            .iter()
            .filter_map(
                |(&pos, errs)| {
                    if pos >= last_pos {
                        Some(errs)
                    } else {
                        None
                    }
                },
            )
            .flatten()
            .cloned()
            .collect()
    }

    fn process_tops(&mut self) {
        let tops = self.stack.take_tops();

        let current_pos = self.stack[tops[0]].pos;

        let tags = tops
            .iter()
            .flat_map(|&s| {
                let entry = self.stack[s];
                &self.table.actions[entry.state.index()]
            })
            .filter_map(|(t, _)| t.as_ref().copied())
            .chain(self.syntax.comment_tags().iter().copied());

        let matched_tokens = self
            .scanner
            .tokens_for_tags(self.input_str, current_pos, tags);

        for top in tops {
            self.process_stack_top(top, matched_tokens.as_slice());
        }
    }

    fn process_stack_top(&mut self, top: StackPos, matched_tokens: &[TokenRes]) {
        let current_entry = self.stack[top];
        let state = current_entry.state;

        let mut match_count = 0;

        for (tag, actions) in &self.table.actions[state.index()] {
            match tag {
                None if current_entry.pos.txt_pos == self.input_str.len() => {
                    match_count += 1;

                    for &action in actions {
                        self.run_action(top, None, action);
                    }
                }
                Some(t) => {
                    let token = matched_tokens
                        .iter()
                        .find(|token| token.token.tag == *t)
                        .copied();

                    if token.is_some() {
                        match_count += 1;

                        for &action in actions {
                            self.run_action(top, token, action);
                        }
                    }
                }
                _ => (),
            }
        }

        if match_count == 0 {
            self.stack.discard(top);
            // TODO: register errors
            //self.register_error(state.index())

            if current_entry.pos.txt_pos < self.input_str.len() {
                if let Some(ignored_token) = self
                    .syntax
                    .ignore_tags()
                    .iter()
                    .filter_map(|&t| {
                        // TODO: build whitespace tokens upfront
                        self.scanner
                            .build_token(self.input_str, current_entry.pos, t)
                    })
                    .next()
                {
                    match_count += 1;
                    let node = self.tree.terminal(ignored_token.token);
                    self.ignore_node(top, node, ignored_token.updated_pos);
                    self.stack.add_to_top(ignored_token.updated_pos, top);
                } else if let Some(comment_token) = self
                    .syntax
                    .comment_tags()
                    .iter()
                    .filter_map(|&t| {
                        // TODO: Use already built comment token
                        self.scanner
                            .build_token(self.input_str, current_entry.pos, t)
                    })
                    .next()
                {
                    match_count += 1;
                    let node = self.build_comment_node(current_entry.pos, comment_token.token);
                    self.ignore_node(top, node, comment_token.updated_pos);
                    self.stack.add_to_top(comment_token.updated_pos, top);
                }
            }
        }

        if match_count == 0 {
            if current_entry.pos.txt_pos < self.input_str.len() {
                self.errors
                    .entry(current_entry.pos.txt_pos)
                    .or_default()
                    .push(ParserError::UnexpectedToken(current_entry.pos, state))
            } else {
                self.errors
                    .entry(current_entry.pos.txt_pos)
                    .or_default()
                    .push(ParserError::UnexpectedEof(current_entry.pos, state))
            }
        }
    }

    fn run_action(&mut self, top: StackPos, token: Option<TokenRes>, action: ParsingAction) {
        let current_entry = self.stack[top];
        match action {
            ParsingAction::Shift(next_state) => {
                let token_res = token.expect("shift action without token");

                let token_node = self.tree.terminal(token_res.token);

                let new_entry = StackEntry::new(token_res.updated_pos, next_state, token_node);

                self.stack.push_entry(top, new_entry);
            }
            ParsingAction::Empty(next_state) => {
                let empty_node = self.tree.empty(current_entry.pos.txt_pos);
                self.stack.push_entry(
                    top,
                    StackEntry::new(current_entry.pos, next_state, empty_node),
                );
            }
            ParsingAction::Reduce(rule, kind, arity, elem) => {
                self.reduce(top, rule, kind, arity, elem);
            }
            ParsingAction::Accept(rule, kind, arity) => {
                self.stack.discard(top);
                for (child_top, childs) in self.collect_child_nodes(top, arity) {
                    self.build_node(current_entry.pos, rule, kind, childs);
                    self.stack.discard(child_top);
                }
                self.accepted = true;
            }
        }
    }

    fn reduce(
        &mut self,
        top: StackPos,
        rule: RuleId,
        kind: KindId,
        arity: usize,
        elem: GrammarElem,
    ) {
        let current_entry = self.stack[top];

        for (pos, childs) in self.collect_child_nodes(top, arity) {
            let pos_entry = self.stack[pos];

            if let Some(entries) = self.table.goto[pos_entry.state.index()].get(&rule) {
                if let Some(node) = self.build_node(current_entry.pos, rule, kind, childs) {
                    for entry in entries {
                        if !entry.forbidden.contains(&elem) {
                            let top_node = if let Some(field_pos) = entry.field {
                                self.tree.named(field_pos, node)
                            } else {
                                node
                            };

                            self.stack.push_entry(
                                pos,
                                StackEntry::new(current_entry.pos, entry.state, top_node),
                            );
                        }
                    }
                }
            } else {
                self.stack.discard(pos)
            }
        }
    }

    fn collect_child_nodes(
        &mut self,
        top: StackPos,
        arity: usize,
    ) -> SmallArrayVec<(StackPos, Vec<TreeNodeId>)> {
        let mut current_states: SmallArrayVec<(StackPos, Vec<TreeNodeId>)> =
            smallvec![(top, vec![])];

        for _ in 0..arity {
            current_states = current_states
                .into_iter()
                .flat_map(|(t, mut childs)| {
                    let top_entry = self.stack[t];

                    if let Some(n) = top_entry.ignore_node {
                        childs.push(n);
                    }

                    childs.push(top_entry.node.unwrap());

                    self.stack
                        .remove_and_get_preds(t)
                        .into_iter()
                        .map(move |new_t| (new_t, childs.clone()))
                })
                .collect();
        }

        current_states
    }

    fn build_node(
        &mut self,
        current_pos: Pos,
        rule: RuleId,
        kind: KindId,
        childs: Vec<TreeNodeId>,
    ) -> Option<TreeNodeId> {
        let mut child_node = None;
        for child in childs.into_iter().rev() {
            child_node = match child_node {
                None => Some(child),
                Some(left) => match self.tree.intermediate(left, child) {
                    None => return None,
                    n => n,
                },
            };
        }

        let constructed_node = self.tree.constructed(current_pos.txt_pos, kind, child_node);

        Some(self.tree.non_terminal(rule, constructed_node))
    }

    fn ignore_node(&mut self, top: StackPos, new_node: TreeNodeId, new_pos: Pos) {
        let current_ignore = self.stack[top].ignore_node;
        let new_ignore_node = self.pack(current_ignore, new_node);
        self.stack[top].ignore_node = new_ignore_node;
        self.stack[top].pos = new_pos;
    }

    fn build_comment_node(&mut self, pos: Pos, token: Token) -> TreeNodeId {
        let comment_token_node = self.tree.terminal(token);
        self.tree.constructed(
            pos.txt_pos,
            COMMENT_NODE_KIND.into(),
            Some(comment_token_node),
        )
    }

    fn pack(&mut self, left: Option<TreeNodeId>, right: TreeNodeId) -> Option<TreeNodeId> {
        left.map(|left_id| self.tree.intermediate(left_id, right))
            .unwrap_or(Some(right))
    }
}

#[cfg(test)]
pub mod tests {
    use indoc::indoc;

    use crate::{
        core::spec::Spec,
        parsing::{sppf::tests::pretty_print_sppf, table::build_table},
    };

    use super::*;

    #[test]
    fn trivial() {
        let spec_str = indoc!(
            "
            node A { }
            rule main = A { 'a' }
        "
        );

        let input = "a";

        let expected = indoc!(
            "main:
            . Alts:
            . . A:
            . . . a"
        );

        test_parser_ok(&spec_str, input, expected);
    }

    #[test]
    fn trivial_ambiguous() {
        let spec_str = indoc!(
            "
            node A { field: B }
            node B { }
            node Bbis { }

            rule main = A { 'a' field@b_node }
            rule b_node = B { 'b' } | Bbis { 'b' }            
        "
        );

        let input = "ab";

        let expected = indoc!(
            "main:
            . Alts:
            . . A:
            . . . a
            . . . FieldPos(0)
            . . . . b_node:
            . . . . . Alts:
            . . . . . . B:
            . . . . . . . b
            . . . . . . Bbis:
            . . . . . . . b"
        );

        test_parser_ok(&spec_str, input, expected);
    }

    #[test]
    fn recursive_rule() {
        let spec_str = indoc!(
            "
            node A { field: A }

            rule main = 
                A { 'a' }
              | A { 'a' field@main }  
        "
        );

        let input = "aa";

        let expected = indoc!(
            "main:
            . Alts:
            . . A:
            . . . a
            . . . FieldPos(0)
            . . . . main:
            . . . . . Alts:
            . . . . . . A:
            . . . . . . . a"
        );

        test_parser_ok(&spec_str, input, expected);
    }

    #[test]
    #[ignore]
    fn invalid_optional() {
        let spec_str = indoc!(
            "
            node A { }
            node B { field1: A, field2: A }
            
            ignore term SPACE = `\\S`

            rule main = B { field1@a_rule? field2@a_rule }

            rule a_rule = A { 'a' }
        "
        );

        let input = "a";

        let expected = indoc!(
            "
            main:
            . Alts:
            . . B:
            . . . ε
            . . . FieldPos(1)
            . . . . a_rule:
            . . . . . Alts:
            . . . . . . A:
            . . . . . . . a"
        );

        test_parser_ok(spec_str, input, expected);
    }

    #[test]
    fn trivial_ambiguous_prefix() {
        let spec_str = indoc!(
            "
            node A { field1: B }
            node B { }
            node Bbis { }

            rule main = 
                A { field1@main 'a' }
              | B { 'b' }  
        "
        );

        let input = "ba";

        let expected = indoc!(
            "main:
            . Alts:
            . . A:
            . . . FieldPos(0)
            . . . . main:
            . . . . . Alts:
            . . . . . . B:
            . . . . . . . b
            . . . a"
        );

        test_parser_ok(&spec_str, input, expected);
    }

    #[test]
    fn tag_alts() {
        let spec = indoc!(
            "
            node A { }
            rule main = A { ['a', 'b'] }
        "
        );

        let expected_a = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . a"
        );

        test_parser_ok(spec, "a", expected_a);

        let expected_b = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . b"
        );

        test_parser_ok(spec, "b", expected_b);
    }

    #[test]
    fn simple_seq() {
        let spec = indoc!(
            "
            node A { }
            rule main = A { `a` `b` `c` }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . a
            . . . b
            . . . c"
        );

        test_parser_ok(spec, "abc", expected);
    }

    #[test]
    #[ignore]
    fn stack_overflow_trigger() {
        let spec = indoc!(
            "
            node A { }
            node B { field: List<A> }

            rule main = A { 'a' } | B { field@main+ }
        "
        );

        // Not fully printed because of the cycle
        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . a
            . . B:
            . . . FieldPos(0)
            . . . . some_main:
            . . . . . Alts:
            . . . . . . List:
            . . . . . . . main:
            . . . . . . . . Alts:
        "
        );

        test_parser_ok(spec, "a", expected);
    }

    #[test]
    fn simple_alt() {
        let spec = indoc!(
            "
            node A { }
            node B { }
            rule main = A { `a` } | B { `b` }
        "
        );

        let expected_b = indoc!(
            "
            main:
            . Alts:
            . . B:
            . . . b"
        );
        test_parser_ok(spec, "b", expected_b);

        let expected_a = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . a"
        );
        test_parser_ok(spec, "a", expected_a);
    }

    #[test]
    fn competing_valid_alterinatives() {
        let spec = indoc!(
            "
            node A1 { }
            node A2 { }
            rule main = A1 { `a` } | A2 { `a` }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A1:
            . . . a
            . . A2:
            . . . a"
        );
        test_parser_ok(spec, "a", expected);
    }

    #[test]
    fn trivial_non_terminal_call() {
        let spec = indoc!(
            "
            node A { }
            node B { }

            rule b_node = B { `b` }
            rule main = A { b_node }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . b_node:
            . . . . Alts:
            . . . . . B:
            . . . . . . b"
        );

        test_parser_ok(spec, "b", expected);
    }

    #[test]
    fn non_terminal_call() {
        let spec = indoc!(
            "
            node A { }
            node B { }

            rule b_node = B { `b` }
            rule main = A { 'a' b_node 'c' }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . a
            . . . b_node:
            . . . . Alts:
            . . . . . B:
            . . . . . . b
            . . . c"
        );
        test_parser_ok(spec, "abc", expected);
    }

    #[test]
    fn trivial_optional_present() {
        let spec = indoc!(
            "
            node A { field: B }

            node B { }

            rule main = A { field@b_node? }
            rule b_node = B { 'b' }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . FieldPos(0)
            . . . . b_node:
            . . . . . Alts:
            . . . . . . B:
            . . . . . . . b"
        );

        test_parser_ok(spec, "b", expected);
    }

    #[test]
    fn trivial_optional_absent() {
        let spec = indoc!(
            "
            node A { field: B }

            node B { }

            rule main = A { field@b_node? }
            rule b_node = B { 'b' }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . ε"
        );

        test_parser_ok(spec, "", expected);
    }

    #[test]
    fn optional_in_seq() {
        let spec = indoc!(
            "
            node A { field1: B, field2: C, field3: D }
            node B { }
            node C { }
            node D { }

            rule main = A { field1@b_node field2@c_node? field3@d_node }
            rule b_node = B { `b` }
            rule c_node = C { `c` }
            rule d_node = D { `d` }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . FieldPos(0)
            . . . . b_node:
            . . . . . Alts:
            . . . . . . B:
            . . . . . . . b
            . . . ε
            . . . FieldPos(2)
            . . . . d_node:
            . . . . . Alts:
            . . . . . . D:
            . . . . . . . d"
        );
        test_parser_ok(spec, "bd", expected);
    }

    #[test]
    fn binop_assoc_left() {
        let spec = indoc!(
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
        );

        let expected = indoc!(
            "
            plus_binop:
            . Alts:
            . . Binop:
            . . . FieldPos(0)
            . . . . plus_binop:
            . . . . . Alts:
            . . . . . . Binop:
            . . . . . . . FieldPos(0)
            . . . . . . . . main:
            . . . . . . . . . Alts:
            . . . . . . . . . . Num:
            . . . . . . . . . . . 1
            . . . . . . . FieldPos(1)
            . . . . . . . . plus:
            . . . . . . . . . Alts:
            . . . . . . . . . . Plus:
            . . . . . . . . . . . +
            . . . . . . . FieldPos(2)
            . . . . . . . . main:
            . . . . . . . . . Alts:
            . . . . . . . . . . Num:
            . . . . . . . . . . . 2
            . . . FieldPos(1)
            . . . . plus:
            . . . . . Alts:
            . . . . . . Plus:
            . . . . . . . +
            . . . FieldPos(2)
            . . . . main:
            . . . . . Alts:
            . . . . . . Num:
            . . . . . . . 3"
        );

        let input = "1+2+3";

        test_parser_ok(spec, input, expected);
    }

    #[test]
    fn binop_assoc_right() {
        let spec = indoc!(
            "
            node Power { }
            node Expr { }
            node Num: Expr { }
            node Binop: Expr { 
                left: Expr,
                op: Power, 
                right: Expr 
            }

            rule power = Power { `\\^` }

            rule main =
                power_binop
              | Num { `[0-9]+` }

            rule power_binop = [right] Binop { left@main op@power right@main }  
        "
        );

        let expected = indoc!(
            "
            power_binop:
            . Alts:
            . . Binop:
            . . . FieldPos(0)
            . . . . main:
            . . . . . Alts:
            . . . . . . Num:
            . . . . . . . 2
            . . . FieldPos(1)
            . . . . power:
            . . . . . Alts:
            . . . . . . Power:
            . . . . . . . ^
            . . . FieldPos(2)
            . . . . power_binop:
            . . . . . Alts:
            . . . . . . Binop:
            . . . . . . . FieldPos(0)
            . . . . . . . . main:
            . . . . . . . . . Alts:
            . . . . . . . . . . Num:
            . . . . . . . . . . . 4
            . . . . . . . FieldPos(1)
            . . . . . . . . power:
            . . . . . . . . . Alts:
            . . . . . . . . . . Power:
            . . . . . . . . . . . ^
            . . . . . . . FieldPos(2)
            . . . . . . . . main:
            . . . . . . . . . Alts:
            . . . . . . . . . . Num:
            . . . . . . . . . . . 8"
        );

        let input = "2^4^8";

        test_parser_ok(spec, input, expected);
    }

    #[test]
    fn binop_precedence() {
        let spec = indoc!(
            "
            node Plus { }
            node Mul { }
            node Num { }
            node Binop { }

            rule plus = Plus { `\\+` }
            rule mul = Mul { `\\*` }

            rule main =
                [1, left] Binop { main plus main } 
              | [2, left] Binop { main mul main } 
              |     Num { `[0-9]+` }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . Binop:
            . . . main:
            . . . . Alts:
            . . . . . Num:
            . . . . . . 1
            . . . plus:
            . . . . Alts:
            . . . . . Plus:
            . . . . . . +
            . . . main:
            . . . . Alts:
            . . . . . Binop:
            . . . . . . main:
            . . . . . . . Alts:
            . . . . . . . . Num:
            . . . . . . . . . 1
            . . . . . . mul:
            . . . . . . . Alts:
            . . . . . . . . Mul:
            . . . . . . . . . *
            . . . . . . main:
            . . . . . . . Alts:
            . . . . . . . . Num:
            . . . . . . . . . 2"
        );

        test_parser_ok(spec, "1+1*2", expected);
    }

    #[test]
    fn very_trivial_list() {
        let spec = indoc!(
            "
            node A { field: List<B> }
            node B { }

            rule main = A { field@b_node+ }
            rule b_node = B { 'b' }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . FieldPos(0)
            . . . . some_b_node:
            . . . . . Alts:
            . . . . . . List:
            . . . . . . . some_b_node:
            . . . . . . . . Alts:
            . . . . . . . . . List:
            . . . . . . . . . . b_node:
            . . . . . . . . . . . Alts:
            . . . . . . . . . . . . B:
            . . . . . . . . . . . . . b
            . . . . . . . b_node:
            . . . . . . . . Alts:
            . . . . . . . . . B:
            . . . . . . . . . . b"
        );
        test_parser_ok(spec, "bb", expected);
    }

    #[test]
    fn trivial_list() {
        let spec = indoc!(
            "
            node A {
                field1: C,
                field2: List<B>,
                field3: C
            }
            node B { }
            node C { }

            rule main = A { field1@c_node field2@b_node+ field3@c_node }
            rule b_node = B { 'b' }
            rule c_node = C { 'c' }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . FieldPos(0)
            . . . . c_node:
            . . . . . Alts:
            . . . . . . C:
            . . . . . . . c
            . . . FieldPos(1)
            . . . . some_b_node:
            . . . . . Alts:
            . . . . . . List:
            . . . . . . . some_b_node:
            . . . . . . . . Alts:
            . . . . . . . . . List:
            . . . . . . . . . . b_node:
            . . . . . . . . . . . Alts:
            . . . . . . . . . . . . B:
            . . . . . . . . . . . . . b
            . . . . . . . b_node:
            . . . . . . . . Alts:
            . . . . . . . . . B:
            . . . . . . . . . . b
            . . . FieldPos(2)
            . . . . c_node:
            . . . . . Alts:
            . . . . . . C:
            . . . . . . . c"
        );
        test_parser_ok(spec, "cbbc", expected);
    }

    #[test]
    #[ignore]
    fn competing_lists() {
        let spec = indoc!(
            "
            node A { 
                first: List<AInner>,
                second: List<AInner>
            }

            node AInner { }

            rule a_inner = AInner { 'a' }  

            rule main = A { first@a_inner* second@a_inner* }
        "
        );

        let expected = indoc!(
            "main:
            . Alts:
            . . A:
            . . . FieldPos(0)
            . . . . list_opt_a_inner:
            . . . . . Alts:
            . . . . . . List
            . . . FieldPos(1)
            . . . . list_opt_a_inner:
            . . . . . Alts:
            . . . . . . List:
            . . . . . . . a_inner:
            . . . . . . . . Alts:
            . . . . . . . . . AInner:
            . . . . . . . . . . a
            . . . . . . . list_opt_a_inner:
            . . . . . . . . Alts:
            . . . . . . . . . List:
            . . . . . . . . . . a_inner:
            . . . . . . . . . . . Alts:
            . . . . . . . . . . . . AInner:
            . . . . . . . . . . . . . a
            . . . . . . . . . List:
            . . . . . . . . . . a_inner:
            . . . . . . . . . . . Alts:
            . . . . . . . . . . . . AInner:
            . . . . . . . . . . . . . a
            . . . . . . . . . . list_opt_a_inner:
            . . . . . . . . . . . Alts:
            . . . . . . . . . . . . List
            . . A:
            . . . FieldPos(0)
            . . . . list_opt_a_inner:
            . . . . . Alts:
            . . . . . . List:
            . . . . . . . a_inner:
            . . . . . . . . Alts:
            . . . . . . . . . AInner:
            . . . . . . . . . . a
            . . . FieldPos(1)
            . . . . list_opt_a_inner:
            . . . . . Alts:
            . . . . . . List:
            . . . . . . . a_inner:
            . . . . . . . . Alts:
            . . . . . . . . . AInner:
            . . . . . . . . . . a
            . . . . . . List:
            . . . . . . . a_inner:
            . . . . . . . . Alts:
            . . . . . . . . . AInner:
            . . . . . . . . . . a
            . . . . . . . list_opt_a_inner:
            . . . . . . . . Alts:
            . . . . . . . . . List"
        );
        test_parser_ok(spec, "a", expected);
    }

    #[test]
    fn empty_sep_by() {
        let spec = indoc!(
            "
            node A { field: List<B> }

            node B { }

            rule b_node = B { `b` }

            rule main = A { field@sepBy(`,`, b_node) }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . FieldPos(0)
            . . . . sepBy_b_node_,_empty:
            . . . . . Alts:
            . . . . . . List"
        );

        test_parser_ok(spec, "", expected);
    }

    #[test]
    fn sep_by_commas() {
        let spec = indoc!(
            "
            node A { field: List<B> }
            node B { }

            rule main = A { field@sepBy(',', b_node) }
            rule b_node = B { 'b' }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . FieldPos(0)
            . . . . sepBy_b_node_,_base:
            . . . . . Alts:
            . . . . . . List:
            . . . . . . . sepBy_b_node_,_base:
            . . . . . . . . Alts:
            . . . . . . . . . List:
            . . . . . . . . . . sepBy_b_node_,_base:
            . . . . . . . . . . . Alts:
            . . . . . . . . . . . . List:
            . . . . . . . . . . . . . b_node:
            . . . . . . . . . . . . . . Alts:
            . . . . . . . . . . . . . . . B:
            . . . . . . . . . . . . . . . . b
            . . . . . . . . . . ,
            . . . . . . . . . . b_node:
            . . . . . . . . . . . Alts:
            . . . . . . . . . . . . B:
            . . . . . . . . . . . . . b
            . . . . . . . ,
            . . . . . . . b_node:
            . . . . . . . . Alts:
            . . . . . . . . . B:
            . . . . . . . . . . b"
        );

        let code = "b,b,b";

        test_parser_ok(spec, code, expected);
    }

    #[test]
    fn sep_by_tr_commas() {
        let spec = indoc!(
            "
            node A { field: List<B> }
            node B { }

            rule main = A { field@sepByTr(',', b_node) }
            rule b_node = B { 'b' }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . FieldPos(0)
            . . . . sepBytr_b_node_,_tr:
            . . . . . Alts:
            . . . . . . List:
            . . . . . . . b_node:
            . . . . . . . . Alts:
            . . . . . . . . . B:
            . . . . . . . . . . b
            . . . . . . . ,
            . . . . . . . sepBytr_b_node_,_tr:
            . . . . . . . . Alts:
            . . . . . . . . . List:
            . . . . . . . . . . b_node:
            . . . . . . . . . . . Alts:
            . . . . . . . . . . . . B:
            . . . . . . . . . . . . . b
            . . . . . . . . . . ,
            . . . . . . . . . . sepBytr_b_node_,_tr:
            . . . . . . . . . . . Alts:
            . . . . . . . . . . . . List:
            . . . . . . . . . . . . . b_node:
            . . . . . . . . . . . . . . Alts:
            . . . . . . . . . . . . . . . B:
            . . . . . . . . . . . . . . . . b
            . . . . . . . . . . . . . ,"
        );

        let code = "b,b,b,";

        test_parser_ok(spec, code, expected);
    }

    #[test]
    fn sep_by_tr_only_one() {
        let spec = indoc!(
            "
            node A { field: List<B> }
            node B { }

            rule main = A { field@sepByTr(',', b_node) }
            rule b_node = B { 'b' }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . FieldPos(0)
            . . . . sepBytr_b_node_,_tr:
            . . . . . Alts:
            . . . . . . List:
            . . . . . . . b_node:
            . . . . . . . . Alts:
            . . . . . . . . . B:
            . . . . . . . . . . b
            . . . . . . . ,"
        );

        let code = "b,";

        test_parser_ok(spec, code, expected);
    }

    #[test]
    fn sep_by_tr_1() {
        let spec = indoc!(
            "
            node A { field: List<B> }

            node B { }

            rule b_node = B { `b` }

            rule main = A { field@sepByTr1(`,`, b_node) }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . FieldPos(0)
            . . . . sepBy1tr_b_node_,_tr:
            . . . . . Alts:
            . . . . . . List:
            . . . . . . . b_node:
            . . . . . . . . Alts:
            . . . . . . . . . B:
            . . . . . . . . . . b
            . . . . . . . ,
            . . . . . . . sepBy1tr_b_node_,_tr:
            . . . . . . . . Alts:
            . . . . . . . . . List:
            . . . . . . . . . . b_node:
            . . . . . . . . . . . Alts:
            . . . . . . . . . . . . B:
            . . . . . . . . . . . . . b
            . . . . . . . . . . ,"
        );

        test_parser_ok(spec, "b,b,", expected);
    }

    #[test]
    fn ignore_whitespace() {
        let spec = indoc!(
            "
            node A { field: List<B> }
            node B {  }

            ignore term WHITESPACE = `\\s`

            rule main = A { field@b_node+ }
            rule b_node = B { 'b' }
        "
        );

        let expected = indoc!(
            "
            main:
            . Alts:
            . . A:
            . . . FieldPos(0)
            . . . . some_b_node:
            . . . . . Alts:
            . . . . . . List:
            . . . . . . . some_b_node:
            . . . . . . . . Alts:
            . . . . . . . . . List:
            . . . . . . . . . . b_node:
            . . . . . . . . . . . Alts:
            . . . . . . . . . . . . B:
            . . . . . . . . . . . . . b
            . . . . . . . . . . . . .  
            . . . . . . . . . . . . .  
            . . . . . . . b_node:
            . . . . . . . . Alts:
            . . . . . . . . . B:
            . . . . . . . . . . b
            . . . . . . . . . .  "
        );

        test_parser_ok(spec, " b  b ", expected);
    }

    #[test]
    fn ambiguous_lexing() {
        let spec = indoc!(
            "
            node A { field: List<Id | False> }
            node False { }
            node Id { }

            ignore term WHITESPACE = `\\s`

            rule main = A { field@a_child+ }
            rule a_child = Id { `[a-z]+` } | False { 'false' }
        "
        );

        let expected = indoc!(
            "
        main:
        . Alts:
        . . A:
        . . . FieldPos(0)
        . . . . some_a_child:
        . . . . . Alts:
        . . . . . . List:
        . . . . . . . some_a_child:
        . . . . . . . . Alts:
        . . . . . . . . . List:
        . . . . . . . . . . some_a_child:
        . . . . . . . . . . . Alts:
        . . . . . . . . . . . . List:
        . . . . . . . . . . . . . a_child:
        . . . . . . . . . . . . . . Alts:
        . . . . . . . . . . . . . . . False:
        . . . . . . . . . . . . . . . . false
        . . . . . . . . . . . . . . . .  
        . . . . . . . . . . a_child:
        . . . . . . . . . . . Alts:
        . . . . . . . . . . . . Id:
        . . . . . . . . . . . . . identifier
        . . . . . . . . . . . . .  
        . . . . . . . a_child:
        . . . . . . . . Alts:
        . . . . . . . . . False:
        . . . . . . . . . . false"
        );

        test_parser_ok(spec, "false identifier false", expected);
    }

    #[test]
    fn nums_grammar() {
        let spec = indoc!(
            "
            node JsonNode { }

            node Array: JsonNode { elems: List<JsonNode> }

            node Number: JsonNode { }

            term NUMBER_LIT = `[0-9]+`

            rule main =
                 Number { NUMBER_LIT }
               | Array { '[' elems@sepBy(',', main) ']' }
        "
        );

        let expected = indoc!(
            "main:
            . Alts:
            . . Array:
            . . . [
            . . . FieldPos(0)
            . . . . sepBy_main_,_base:
            . . . . . Alts:
            . . . . . . List:
            . . . . . . . sepBy_main_,_base:
            . . . . . . . . Alts:
            . . . . . . . . . List:
            . . . . . . . . . . main:
            . . . . . . . . . . . Alts:
            . . . . . . . . . . . . Number:
            . . . . . . . . . . . . . 1
            . . . . . . . ,
            . . . . . . . main:
            . . . . . . . . Alts:
            . . . . . . . . . Array:
            . . . . . . . . . . [
            . . . . . . . . . . FieldPos(0)
            . . . . . . . . . . . sepBy_main_,_base:
            . . . . . . . . . . . . Alts:
            . . . . . . . . . . . . . List:
            . . . . . . . . . . . . . . main:
            . . . . . . . . . . . . . . . Alts:
            . . . . . . . . . . . . . . . . Number:
            . . . . . . . . . . . . . . . . . 1
            . . . . . . . . . . ]
            . . . ]"
        );

        test_parser_ok(spec, "[1,[1]]", expected)
    }

    fn test_parser_ok(spec_code: &str, input: &str, expected: &str) {
        let spec_ast = sylver_dsl::meta::parse(spec_code.as_ref()).expect("Invalid spec str");
        let spec = Spec::from_decls(spec_ast).expect("Invalid spec");

        let rules = spec
            .syntax
            .terminals()
            .map(|(id, decl)| (spec.syntax.decl_position(id.into()), id, decl.reg.clone()));

        let table = build_table(&spec.syntax, "main").unwrap();
        println!("{}", table.render(&spec.syntax));

        let scanner =
            Scanner::new(rules.into_iter().map(|(_, tag, content)| (tag, content))).unwrap();

        let mut parser = Parser::new(&spec.syntax, &table, &scanner, input);

        parser.parse();

        assert_eq!(expected, pretty_print_sppf(&spec, &parser.tree, input));
    }
}
