use std::{
    cmp::Ordering, collections::HashMap, fs::read_to_string, hash::Hash, ops::Index, path::Path,
    path::PathBuf,
};

use anyhow::Context;
use derive_more::{From, Into};
use id_vec::Id;
use itertools::Itertools;
use smallvec::SmallVec;
use thiserror::Error;

use sylver_dsl::meta::*;

use crate::{
    id_type,
    script::{
        python::{PythonScript, PythonScriptEngine},
        ScriptEngine,
    },
    util::{intern_map::StrIdMap, once::OnceQueue},
};

pub const DEFAULT_START_RULE: &str = "main";

const COMMENT_NODE_KIND_NAME: &str = "Comment";
pub const COMMENT_NODE_KIND: usize = 0;

pub const BUILTIN_LIST_KIND_NAME: &str = "List";
pub const BUILTIN_LIST_KIND: usize = 1;

pub const ERROR_KIND_NAME: &str = "Error";
pub const ERROR_KIND: usize = 2;

pub const UNKNOWN_TAG_NAME: &str = "Unknown";
pub const UNKNOWN_TAG: usize = 3;

#[derive(Debug, Error, Eq, PartialEq, Clone, Hash)]
pub enum SpecErr {
    #[error("Multiple uses of name {0}")]
    MultipleDecl(String),
    #[error("Unknown symbol: {0}")]
    MissingDecl(String),
}

pub type SpecRes<T> = Result<T, SpecErr>;

id_type!(TagId: String);
id_type!(KindId: String);
id_type!(RuleId: String);
id_type!(SpecId: Spec);

pub type TagVec = SmallVec<[TagId; 2]>;

#[derive(Debug, Copy, Clone, From, Into, Eq, PartialEq, Hash)]
pub struct FieldPos(usize);

/// Represents a language specification.
#[derive(Debug, Clone, PartialEq)]
pub struct Spec {
    /// Syntax related structures.
    pub syntax: Syntax,
    // Named aspects.
    pub aspects: Aspects,
}

impl Spec {
    /// Build a spec with the given language syntax.
    pub fn new(aspects: Aspects, syntax: Syntax) -> Spec {
        Spec { aspects, syntax }
    }

    /// Create a `Spec` from a slice of rule declarations.
    pub fn from_decls(aspects: Aspects, decls: impl IntoIterator<Item = Decl>) -> SpecRes<Spec> {
        let syntax = SyntaxBuilder::new().build(decls)?;
        Ok(Spec { aspects, syntax })
    }

    /// Return the kind ids of all child kinds.
    pub fn child_kinds(&self, kind: KindId) -> Vec<KindId> {
        let mut result = vec![];

        let mut queue: OnceQueue<KindId> = self.direct_descending_kinds(kind).into_iter().collect();
        while let Some(child_kind) = queue.pop() {
            result.push(child_kind);
            queue.extend(self.direct_descending_kinds(child_kind));
        }

        result
    }

    fn direct_descending_kinds(&self, kind: KindId) -> Vec<KindId> {
        self.syntax
            .nodes(false)
            .filter(|n| {
                matches!(
                    n.parent_type,
                    Some(ref parent_name) if parent_name == self.syntax.kind_name(kind)
                )
            })
            .map(|n| self.syntax.kind_id(&n.name).unwrap())
            .collect()
    }

    /// Return the kind ids of all parent kinds.
    pub fn parent_kinds(&self, kind: KindId) -> Vec<KindId> {
        let mut result = vec![];

        let mut kind_name = &self.syntax[kind].parent_type;
        while let Some(name) = kind_name {
            let parent_kind = self.syntax.kind_id(name).unwrap();

            result.push(parent_kind);

            kind_name = &self.syntax[parent_kind].parent_type;
        }

        result
    }
}

pub fn spec_from_files(
    engine: &PythonScriptEngine,
    aspects_file: Option<&PathBuf>,
    spec_file: &Path,
) -> anyhow::Result<Spec> {
    let spec_str = read_to_string(spec_file)
        .with_context(|| format!("Could not read spec file: {}", spec_file.display()))?;

    let syntax = SyntaxBuilder::new().build(parse(&spec_str)?)?;

    let aspects = Aspects::build(&syntax, raw_aspect_from_file(engine, aspects_file)?)?;

    Ok(Spec::new(aspects, syntax))
}

fn raw_aspect_from_file(
    engine: &PythonScriptEngine,
    aspects: Option<&PathBuf>,
) -> anyhow::Result<HashMap<String, HashMap<String, PythonScript>>> {
    Ok(aspects
        .map(|f| {
            let aspects_script = read_to_string(f)
                .with_context(|| format!("Could not read aspects file: {}", f.display()))?;

            engine
                .compile_aspects(&aspects_script, &f.display().to_string())
                .with_context(|| format!("Could not compile aspects file: {}", f.display()))
        })
        .transpose()?
        .unwrap_or_default())
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct Aspects {
    scripts: HashMap<(String, KindId), PythonScript>,
}

impl Aspects {
    pub fn build(
        syntax: &Syntax,
        invokables: HashMap<String, HashMap<String, PythonScript>>,
    ) -> anyhow::Result<Self> {
        let mut aspect_scripts = HashMap::new();

        for (aspect_name, scripts) in invokables {
            for (kind_name, script) in scripts {
                let kind = syntax.kind_id(&kind_name).with_context(|| {
                    format!("can't add aspect {aspect_name} to non_existing kind {kind_name}")
                })?;
                aspect_scripts.insert((aspect_name.clone(), kind), script);
            }
        }

        Ok(Aspects {
            scripts: aspect_scripts,
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
enum SyntaxDecl {
    Syntactic(Decl),
    Synthetic(Decl),
}

impl SyntaxDecl {
    fn as_decl(&self) -> Option<&Decl> {
        match self {
            SyntaxDecl::Syntactic(d) | SyntaxDecl::Synthetic(d) => Some(d),
        }
    }

    fn as_mut_decl(&mut self) -> Option<&mut Decl> {
        match self {
            SyntaxDecl::Syntactic(d) | SyntaxDecl::Synthetic(d) => Some(d),
        }
    }

    fn as_mut_rule_decl(&mut self) -> Option<&mut RuleDecl> {
        self.as_mut_decl().and_then(|d| match d {
            Decl::Rule(r) => Some(r),
            _ => None,
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Syntax {
    // Vec containing the comment tags, followed by the ignore tags.
    trivial_tags: Vec<TagId>,
    comment_tags_count: usize,
    declarations: StrIdMap<SyntaxDecl>,
}

impl Syntax {
    /// Return the ignore tags.
    pub fn ignore_tags(&self) -> &[TagId] {
        &self.trivial_tags[self.comment_tags_count..]
    }

    /// Return the commend tags.
    pub fn comment_tags(&self) -> &[TagId] {
        &self.trivial_tags[0..self.comment_tags_count]
    }

    /// Return a slice containing the comment tags, followed by the ignore tags.
    pub fn trivial_tags(&self) -> &[TagId] {
        &self.trivial_tags
    }

    /// Return the declaration associated with the given name, if it exists.
    pub fn decl_from_name(&self, name: &str) -> Option<&Decl> {
        self.declarations.get_key(name).and_then(|d| d.as_decl())
    }

    /// Return the declaration associated with the given id, if it exists.
    pub fn decl_from_id(&self, id: Id<String>) -> Option<&Decl> {
        self.declarations.get(id).and_then(|d| d.as_decl())
    }

    /// Return the order of the given declaration in the spec.
    pub fn decl_position(&self, id: Id<String>) -> usize {
        self.declarations.insertion_order(id)
    }

    /// Return an iterator over the spec's node declarations.
    pub fn nodes(&self, with_synthetics: bool) -> impl Iterator<Item = &NodeDecl> {
        self.declarations
            .values()
            .filter_map(move |n| retain_node(n, with_synthetics))
    }

    /// Return an iterator over all of the node field names;
    pub fn field_names(&self) -> impl Iterator<Item = &str> {
        self.nodes(false)
            .flat_map(|n| n.fields.keys())
            .map(|k| k.as_str())
    }

    /// Return the id of the given type.
    pub fn kind_id(&self, name: impl AsRef<str>) -> Option<KindId> {
        let id = self.declarations.get_id(name.as_ref())?;

        match self.declarations.get(id) {
            Some(SyntaxDecl::Syntactic(Decl::Node(_)) | SyntaxDecl::Synthetic(Decl::Node(_))) => {
                Some(id.into())
            }
            _ => None,
        }
    }

    // Same as `kind_id`, but panics if the requested kind does not exist.
    pub fn existing_kind_id(&self, name: impl AsRef<str>) -> KindId {
        self.kind_id(strip_list_kind(name.as_ref()))
            .unwrap_or_else(|| panic!("Invalid kind name: {}", name.as_ref()))
    }

    /// Return the kind id representing lists of elements of the given kind.
    pub fn list_kind(&self) -> KindId {
        BUILTIN_LIST_KIND.into()
    }

    /// Return whether the given kind is a list kind.
    pub fn is_list_kind(&self, kind: KindId) -> bool {
        kind.index() == BUILTIN_LIST_KIND
    }

    #[allow(dead_code)]
    fn node_decl(&self, kind_name: &str) -> Option<&NodeDecl> {
        self.declarations
            .get_key(kind_name)
            .and_then(|n| retain_node(n, true))
    }

    /// Return an iterator over the spec's terminal declarations.
    pub fn terminals(&self) -> impl Iterator<Item = (TagId, &TermDecl)> {
        self.declarations
            .iter()
            .filter_map(|(id, decl)| retain_term(decl).map(|t| (TagId::from(id.index_value()), t)))
    }

    /// Return the id of the terminal rule with the given name.
    /// # Panic
    /// If the name doesn't match a declaration or if the matching declaration
    /// is not a terminal rule.
    pub fn tag_id(&self, name: impl AsRef<str>) -> TagId {
        self.get_opt_terminal_id(name.as_ref())
            .unwrap_or_else(|| panic!("No terminal rule named: {}", name.as_ref()))
    }

    #[allow(dead_code)]
    pub fn terminal(&self, tag_name: &str) -> Option<&TermDecl> {
        self.declarations.get_key(tag_name).and_then(retain_term)
    }

    /// Return an iterator over the spec's rule declarations.
    pub fn rules(&self) -> impl Iterator<Item = &RuleDecl> {
        self.declarations.values().filter_map(retain_rule)
    }

    /// Return a iterator over the rules ids.
    pub fn rules_ids(&'_ self) -> impl '_ + Iterator<Item = RuleId> {
        self.declarations
            .iter()
            .filter(|(_, decl)| matches!(decl, SyntaxDecl::Syntactic(Decl::Rule(_))))
            .map(|(id, _)| id.into())
    }

    pub fn get_rule_id(&self, name: impl AsRef<str>) -> Option<RuleId> {
        let id = self.declarations.get_id(name.as_ref())?;

        match self.syntactic_decl(id) {
            Some(Decl::Rule(_)) => Some(id.into()),
            _ => None,
        }
    }

    /// Return the id of the rule with the given name.
    /// # Panic
    /// If the name doesn't match a declaration or if the matching declaration
    /// is not a non-terminal rule.
    pub fn rule_id(&self, name: impl AsRef<str>) -> RuleId {
        let id = self
            .declarations
            .get_id(name.as_ref())
            .unwrap_or_else(|| panic!("Invalid declaration name: {}", name.as_ref()));

        match self.declarations.get(id) {
            Some(SyntaxDecl::Syntactic(Decl::Rule(_)) | SyntaxDecl::Synthetic(Decl::Rule(_))) => (),
            _ => panic!("'{}' is not a non-terminal name", name.as_ref()),
        }

        id.into()
    }

    /// Return this id of the given field name.
    /// # panics
    /// If there is no field with the given name.
    pub fn field_position(&self, kind: KindId, name: impl AsRef<str>) -> Option<FieldPos> {
        self[kind]
            .fields
            .keys()
            .position(|n| n == name.as_ref())
            .map(Into::into)
    }

    /// Return the id of the field at the given position in nodes of a given kind, if it exists.
    pub fn field_name(&'_ self, kind: KindId, pos: FieldPos) -> Option<&str> {
        self[kind]
            .fields
            .keys()
            .nth(pos.into())
            .map(|name| name.as_str())
    }

    /// Return the type of a given field.
    pub fn field_type(&self, kind: KindId, pos: FieldPos) -> Option<&TypeLit> {
        // TODO: if the entries are in the same order as the keys, one lookup can be avoided...
        self[kind]
            .fields
            .keys()
            .nth(pos.into())
            .map(|k| &self[kind].fields[k])
    }

    fn get_opt_terminal_id(&self, name: impl AsRef<str>) -> Option<TagId> {
        self.declarations
            .get_id(name.as_ref())
            .filter(|&id| matches!(self.syntactic_decl(id), Some(Decl::Terminal(_))))
            .map(|id| id.into())
    }

    /// Return the node type associated with the given `KindId`.
    pub fn kind_name(&self, kind: KindId) -> &str {
        self.declarations
            .key_for_id(kind.into())
            .unwrap_or_else(|| panic!("No kind name for kind id: {kind:?}"))
    }

    /// Return the name of the term declaration associated with the given `TagId`.
    pub fn tag_name(&self, tag: TagId) -> &str {
        &self[tag].name
    }

    /// Return the kind associated with comment nodes.
    pub fn comment_kind(&self) -> KindId {
        COMMENT_NODE_KIND.into()
    }

    fn syntactic_decl(&self, id: Id<String>) -> Option<&Decl> {
        match self.declarations.get(id) {
            Some(SyntaxDecl::Syntactic(d)) => Some(d),
            _ => None,
        }
    }
}

impl Index<KindId> for Syntax {
    type Output = NodeDecl;

    fn index(&self, index: KindId) -> &Self::Output {
        self.declarations
            .get(index.into())
            .and_then(|n| retain_node(n, true))
            .unwrap_or_else(|| panic!("No node with index {index:?}"))
    }
}

impl Index<RuleId> for Syntax {
    type Output = RuleDecl;

    fn index(&self, index: RuleId) -> &Self::Output {
        self.declarations
            .get(index.into())
            .and_then(retain_rule)
            .unwrap_or_else(|| panic!("No rule with index {index:?}"))
    }
}

impl Index<TagId> for Syntax {
    type Output = TermDecl;

    fn index(&self, index: TagId) -> &Self::Output {
        self.declarations
            .get(index.into())
            .and_then(retain_term)
            .unwrap_or_else(|| panic!("No term rule with index: {index:?}"))
    }
}

#[derive(Debug, Clone)]
pub struct SyntaxBuilder {
    declarations: StrIdMap<SyntaxDecl>,
    ignore_tags: Vec<TagId>,
    comment_tags: Vec<TagId>,
}

impl SyntaxBuilder {
    pub fn new() -> SyntaxBuilder {
        let mut declarations = StrIdMap::new();

        let builtin_kinds: [&str; 4] = [
            COMMENT_NODE_KIND_NAME,
            BUILTIN_LIST_KIND_NAME,
            ERROR_KIND_NAME,
            UNKNOWN_TAG_NAME,
        ];

        for kind_name in builtin_kinds {
            declarations.insert(
                kind_name.into(),
                SyntaxDecl::Synthetic(Decl::Node(NodeDecl {
                    name: kind_name.into(),
                    parent_type: None,
                    fields: Default::default(),
                })),
            );
        }

        SyntaxBuilder {
            declarations,
            ignore_tags: vec![],
            comment_tags: vec![],
        }
    }

    pub fn build(mut self, decls: impl IntoIterator<Item = Decl>) -> SpecRes<Syntax> {
        for decl in decls {
            self.insert_decl(decl)?;
        }

        self.validate()?;

        self.collect_special_tags();

        self.expand_calls();

        // self.create_or_type_decls();

        let trivial_tags = self
            .comment_tags
            .iter()
            .chain(self.ignore_tags.iter())
            .copied()
            .collect();

        Ok(Syntax {
            trivial_tags,
            declarations: self.declarations,
            comment_tags_count: self.comment_tags.len(),
        })
    }

    fn collect_special_tags(&mut self) {
        for (id, decl) in self.declarations.iter() {
            if let SyntaxDecl::Syntactic(Decl::Terminal(TermDecl {
                data: Some(term_data),
                ..
            })) = decl
            {
                match term_data {
                    TermDeclData::Ignore => self.ignore_tags.push(id.into()),
                    TermDeclData::Comment => self.comment_tags.push(id.into()),
                }
            }
        }
    }

    fn insert_decl(&mut self, decl: Decl) -> SpecRes<()> {
        if let Decl::Rule(r) = &decl {
            self.add_inline_regs(r)?;
        }

        self.insert_if_not_exists(false, decl)?;

        Ok(())
    }

    fn add_inline_regs(&mut self, decl: &RuleDecl) -> SpecRes<()> {
        let inline_regs = collect_inline_regs(decl);

        for r in inline_regs {
            self.insert_if_not_exists(
                true,
                Decl::Terminal(TermDecl {
                    name: r.as_str().into(),
                    reg: r.clone(),
                    data: None,
                }),
            )?;
        }

        Ok(())
    }

    fn validate(&self) -> SpecRes<()> {
        let rules = self.declarations.values().filter_map(retain_rule);

        for rule in rules {
            for alternative in &rule.alternatives {
                self.validate_alternative(alternative)?;
            }
        }

        Ok(())
    }

    fn validate_alternative(&self, alternative: &RuleExpr) -> SpecRes<()> {
        match alternative {
            RuleExpr::Node(n) => self.validate_node_alternative(n),
            RuleExpr::Ref(r) => self.validate_ref_alternative(r),
        }
    }

    fn validate_node_alternative(&self, alternative: &NodeRuleExpr) -> SpecRes<()> {
        self.assert_node_exists(alternative.node_type())?;

        for comp in &alternative.comps {
            if let AlternativeComp::RuleRef(name) = comp {
                self.assert_rule_exists(name)
                    .or_else(|_| self.assert_term_exists(name))?
            }
        }

        Ok(())
    }

    fn validate_ref_alternative(&self, alternative: &RuleExprRef) -> SpecRes<()> {
        self.assert_rule_exists(&alternative.rule_name)
    }

    fn assert_rule_exists(&self, name: &str) -> SpecRes<()> {
        self.assert_exists_syntactic(name, |d| d.is_rule())
    }

    fn assert_term_exists(&self, name: &str) -> SpecRes<()> {
        self.assert_exists_syntactic(name, |d| d.is_term())
    }

    fn assert_node_exists(&self, name: &str) -> SpecRes<()> {
        self.assert_exists_syntactic(name, |d| d.is_node())
    }

    fn assert_exists_syntactic(
        &self,
        name: &str,
        predicate: impl Fn(&Decl) -> bool,
    ) -> SpecRes<()> {
        if self
            .declarations
            .get_key(name)
            .and_then(SyntaxDecl::as_decl)
            .filter(|d| predicate(d))
            .is_none()
        {
            return Err(SpecErr::MissingDecl(name.to_string()));
        }
        Ok(())
    }

    fn insert_if_not_exists(&mut self, allow_duplicates: bool, decl: Decl) -> SpecRes<()> {
        let name = decl.name().to_string();

        match self
            .declarations
            .insert(name.clone(), SyntaxDecl::Syntactic(decl.clone()))
        {
            (_, Some(SyntaxDecl::Syntactic(d))) if !allow_duplicates || d != decl => {
                Err(SpecErr::MultipleDecl(name))
            }
            _ => Ok(()),
        }
    }

    fn expand_calls(&mut self) {
        let comps: Vec<CompExpr> = self
            .declarations
            .values_mut()
            .filter_map(SyntaxDecl::as_mut_rule_decl)
            .flat_map(|expr| expr.alternatives.iter_mut())
            .filter_map(RuleExpr::as_mut_node)
            .flat_map(|n| n.comps.iter_mut())
            .filter_map(|comp| match comp {
                AlternativeComp::Full(
                    _,
                    expr @ (CompExpr::SepBy(_) | CompExpr::Some(_) | CompExpr::Many(_)),
                ) => {
                    let name = call_name(expr);
                    let replaced_expr = std::mem::replace(expr, CompExpr::Ref(name));
                    Some(replaced_expr)
                }
                _ => None,
            })
            .collect();

        for expr in &comps {
            let name = call_name(expr);
            self.create_comp_rules(&name, expr);
        }
    }

    fn create_comp_rules(&mut self, rule_name: &str, expr: &CompExpr) {
        match expr {
            CompExpr::Many(r) => self.make_list_rule(rule_name, r, true),
            CompExpr::Some(r) => self.make_list_rule(rule_name, r, false),
            CompExpr::SepBy(s) => self.make_sep_by_rule(rule_name, s),
            _ => {}
        }
    }

    fn make_list_rule(&mut self, rule_name: &str, non_term_name: &str, allow_empty: bool) {
        if self.declarations.get_key(rule_name).is_some() {
            return;
        }

        let rec_name = if allow_empty {
            format!("{rule_name}_base")
        } else {
            rule_name.to_string()
        };

        let alternatives = vec![
            list_node_rule_expr(vec![AlternativeComp::RuleRef(non_term_name.to_string())]),
            list_node_rule_expr(vec![
                AlternativeComp::RuleRef(rec_name.clone()),
                AlternativeComp::RuleRef(non_term_name.to_string()),
            ]),
        ];

        if allow_empty {
            let empty_alternative_name = format!("{rule_name}_empty");
            self.create_rule(&empty_alternative_name, vec![list_node_rule_expr(vec![])]);

            self.create_rule(&rec_name, alternatives);

            self.create_rule(
                rule_name,
                vec![
                    rule_expr_ref(&empty_alternative_name),
                    rule_expr_ref(&rec_name),
                ],
            )
        } else {
            self.create_rule(rule_name, alternatives);
        }
    }

    fn make_sep_by_rule(&mut self, rule_name: &str, data: &SepByData) {
        if self.declarations.get_key(rule_name).is_some() {
            return;
        }

        let rec_name = if data.trailing || data.allow_empty {
            format!("{rule_name}_base")
        } else {
            rule_name.to_string()
        };

        let base_alternatives = vec![
            list_node_rule_expr(vec![AlternativeComp::RuleRef(data.rule_name.clone())]),
            list_node_rule_expr(vec![
                AlternativeComp::RuleRef(rec_name.to_string()),
                AlternativeComp::TExpr(data.term.clone()),
                AlternativeComp::RuleRef(data.rule_name.clone()),
            ]),
        ];

        let tr_name = format!("{rule_name}_tr");

        let tr_alternative = if data.trailing {
            vec![
                list_node_rule_expr(vec![
                    AlternativeComp::RuleRef(data.rule_name.clone()),
                    AlternativeComp::TExpr(data.term.clone()),
                    AlternativeComp::RuleRef(tr_name.to_string()),
                ]),
                list_node_rule_expr(vec![
                    AlternativeComp::RuleRef(data.rule_name.clone()),
                    AlternativeComp::TExpr(data.term.clone()),
                ]),
            ]
        } else {
            vec![]
        };

        self.make_sepby_from_partials(
            rule_name,
            &rec_name,
            &tr_name,
            base_alternatives,
            data.allow_empty,
            tr_alternative,
        );
    }

    fn make_sepby_from_partials(
        &mut self,
        rule_name: &str,
        rec_name: &str,
        tr_name: &str,
        base_alternative: Vec<RuleExpr>,
        has_empty_alternative: bool,
        tr_alternative: Vec<RuleExpr>,
    ) {
        if !has_empty_alternative && tr_alternative.is_empty() {
            self.create_rule(rule_name, base_alternative);
        } else {
            self.create_rule(rec_name, base_alternative);

            let mut alternatives = vec![rec_name.to_string()];

            if has_empty_alternative {
                let empty_alternative_name = format!("{rule_name}_empty");
                self.create_rule(&empty_alternative_name, vec![list_node_rule_expr(vec![])]);
                alternatives.push(empty_alternative_name)
            }

            if !tr_alternative.is_empty() {
                self.create_rule(tr_name, tr_alternative);
                alternatives.push(tr_name.to_string());
            }

            self.create_rule(
                rule_name,
                alternatives
                    .into_iter()
                    .map(|n| RuleExpr::Ref(RuleExprRef { rule_name: n }))
                    .collect(),
            )
        }
    }

    fn create_rule(&mut self, rule_name: &str, alternatives: Vec<RuleExpr>) {
        self.declarations.insert(
            rule_name.to_string(),
            SyntaxDecl::Synthetic(Decl::Rule(RuleDecl {
                name: rule_name.to_string(),
                alternatives,
            })),
        );
    }
}

// Given a kind name of the form: 'List<type>', return 'type'.
pub fn strip_list_kind(kind_name: &str) -> String {
    let list_regex = fancy_regex::Regex::new("List<(.*)>").unwrap();

    let stripped = if let Some(Ok(capture)) = list_regex.captures_iter(kind_name).next() {
        capture[1].to_string()
    } else {
        kind_name.to_string()
    };

    stripped
}

fn call_name(expr: &CompExpr) -> String {
    match expr {
        CompExpr::Some(s) => format!("some_{s}"),
        CompExpr::Many(s) => format!("many_{s}"),
        CompExpr::SepBy(s) => {
            let empty = if s.allow_empty { "" } else { "1" };
            let trailing = if s.trailing { "tr" } else { "" };
            let rule = &s.rule_name;
            let term = match &s.term {
                TermExpr::Ref(s) => s.clone(),
                TermExpr::Content(c) => c.as_str().to_string(),
                TermExpr::Alts(alts) => alts.iter().map(|a| a.as_str()).join("_"),
            };
            format!("sepBy{empty}{trailing}_{rule}_{term}")
        }
        _ => panic!("No call name for unquantified expr: {expr:?}"),
    }
}

fn collect_inline_regs(decl: &RuleDecl) -> impl Iterator<Item = &TermContent> {
    decl.alternatives
        .iter()
        .filter_map(|a| a.as_node())
        .flat_map(|n| inline_regs_in_comps(&n.comps))
}

fn inline_regs_in_comps(comps: &[AlternativeComp]) -> impl Iterator<Item = &TermContent> {
    comps.iter().flat_map(|c| match c {
        AlternativeComp::TExpr(e) => inline_regs_in_term_expr(e),
        AlternativeComp::Full(_, CompExpr::SepBy(SepByData { term, .. })) => {
            inline_regs_in_term_expr(term)
        }
        _ => vec![],
    })
}

fn inline_regs_in_term_expr(expr: &TermExpr) -> Vec<&TermContent> {
    match expr {
        TermExpr::Content(c) => vec![c],
        TermExpr::Alts(alts) => alts.iter().filter_map(|a| a.as_term_content()).collect(),
        _ => vec![],
    }
}

/// If the given declaration is a terminal declaration, return the unwraped terminal declaration.
/// Otherwise return `None`.
fn retain_term(decl: &SyntaxDecl) -> Option<&TermDecl> {
    match decl {
        SyntaxDecl::Syntactic(Decl::Terminal(t)) => Some(t),
        _ => None,
    }
}

/// If the given declaration is a rule declaration, return the unwraped rule declaration.
/// Otherwise return `None`.
fn retain_rule(decl: &SyntaxDecl) -> Option<&RuleDecl> {
    match decl {
        SyntaxDecl::Syntactic(Decl::Rule(r)) | SyntaxDecl::Synthetic(Decl::Rule(r)) => Some(r),
        _ => None,
    }
}

/// If the given declaration is a node declaration, return the unwraped node declaration.
/// Otherwise return `None`.
fn retain_node(decl: &SyntaxDecl, with_synthetics: bool) -> Option<&NodeDecl> {
    match decl {
        SyntaxDecl::Syntactic(Decl::Node(n)) => Some(n),
        SyntaxDecl::Synthetic(Decl::Node(n)) if with_synthetics => Some(n),
        _ => None,
    }
}

fn list_node_rule_expr(comps: Vec<AlternativeComp>) -> RuleExpr {
    RuleExpr::Node(NodeRuleExpr {
        prec: None,
        node_type: BUILTIN_LIST_KIND_NAME.to_string(),
        comps,
    })
}

fn rule_expr_ref(rule_name: &str) -> RuleExpr {
    RuleExpr::Ref(RuleExprRef {
        rule_name: rule_name.to_string(),
    })
}

impl Default for SyntaxBuilder {
    fn default() -> Self {
        SyntaxBuilder::new()
    }
}

#[cfg(test)]
pub mod test {
    use std::collections::HashSet;

    use indoc::indoc;
    use maplit::hashset;

    use sylver_dsl::meta::parse;

    use super::*;

    #[test]
    fn field_names() {
        let spec = parse_spec(indoc!(
            "
            node Node1 { field1: Node2 }
            node Node2 { field2: Node1 }
        "
        ));

        assert_eq!(
            hashset! { "field1", "field2" },
            spec.syntax.field_names().collect()
        )
    }

    #[test]
    fn child_kinds() {
        let spec = parse_spec(indoc!(
            "
            node ParentNode { }
            node Child1: ParentNode { }
            node Child2: ParentNode { }
            node Child3: Child1 { }
        "
        ));

        let parent_kind = spec.syntax.kind_id("ParentNode").unwrap();
        let child1_kind = spec.syntax.kind_id("Child1").unwrap();
        let child2_kind = spec.syntax.kind_id("Child2").unwrap();
        let child3_kind = spec.syntax.kind_id("Child3").unwrap();

        assert_eq!(
            hashset! { child2_kind, child1_kind, child3_kind },
            spec.child_kinds(parent_kind).into_iter().collect()
        );

        assert_eq!(&[child3_kind], spec.child_kinds(child1_kind).as_slice());

        assert!(spec.child_kinds(child2_kind).is_empty());
        assert!(spec.child_kinds(child3_kind).is_empty());
    }

    #[test]
    fn parent_kinds() {
        let spec = parse_spec(indoc!(
            "
            node ParentNode { }
            node ChildNode: ParentNode { }
        "
        ));

        let parent_kind = spec.syntax.kind_id("ParentNode").unwrap();
        let child_kind = spec.syntax.kind_id("ChildNode").unwrap();

        assert_eq!(&[] as &[KindId], spec.parent_kinds(parent_kind).as_slice());
        assert_eq!(&[parent_kind], spec.parent_kinds(child_kind).as_slice());
    }

    #[test]
    fn comment_kind() {
        let builder = SyntaxBuilder::new();

        assert_eq!(
            Some(&SyntaxDecl::Synthetic(Decl::Node(NodeDecl {
                name: COMMENT_NODE_KIND_NAME.into(),
                parent_type: None,
                fields: Default::default(),
            }))),
            builder.declarations.get(Id::from_index(COMMENT_NODE_KIND))
        );

        assert_eq!(
            Some(&COMMENT_NODE_KIND_NAME.to_string()),
            builder
                .declarations
                .key_for_id(Id::from_index(COMMENT_NODE_KIND))
        );
    }

    #[test]
    fn builtin_list_kind() {
        let builder = SyntaxBuilder::new();

        assert_eq!(
            Some(&SyntaxDecl::Synthetic(Decl::Node(NodeDecl {
                name: BUILTIN_LIST_KIND_NAME.into(),
                parent_type: None,
                fields: Default::default(),
            }))),
            builder.declarations.get(Id::from_index(BUILTIN_LIST_KIND))
        );

        assert_eq!(
            Some(&BUILTIN_LIST_KIND_NAME.to_string()),
            builder
                .declarations
                .key_for_id(Id::from_index(BUILTIN_LIST_KIND))
        );
    }

    #[test]
    fn test_load_spec() {
        let spec_str = "\
            term NUM = `\\d+`
            term COMA = `,`
        ";

        let syntax = get_syntax(spec_str);

        assert_eq!(2, syntax.terminals().count());
        assert!(syntax.terminal("NUM").is_some());
        assert!(syntax.terminal("COMA").is_some())
    }

    #[test]
    fn test_load_kinds() {
        let spec_str = indoc!(
            "
           node Binop { }
        "
        );

        let syntax = get_syntax(spec_str);

        assert_eq!(1, syntax.nodes(false).count());
        assert!(syntax.node_decl("Binop").is_some());
    }

    #[test]
    fn invalid_multiple_node_decls() {
        let spec_str = indoc!(
            "\
            node Binop { }
            node Binop { }
        "
        );

        let res = SyntaxBuilder::new().build(parse_decls(spec_str));

        assert_eq!(Err(SpecErr::MultipleDecl("Binop".into())), res);
    }

    #[test]
    fn invalid_multiple_term_decls() {
        let spec_str = indoc!(
            "\
            term LPAR = `\\(`
            term LPAR = `\\(`
        "
        );

        let res = SyntaxBuilder::new().build(parse_decls(spec_str));

        assert_eq!(Err(SpecErr::MultipleDecl("LPAR".into())), res);
    }

    #[test]
    fn missing_node_decl() {
        let spec_str = indoc!(
            "
            rule hello = HelloNode { `nodeContent` }
        "
        );

        let res = SyntaxBuilder::new().build(parse_decls(spec_str));

        assert_eq!(Err(SpecErr::MissingDecl("HelloNode".into())), res);
    }

    #[test]
    fn missing_term_decl() {
        let spec_str = indoc!(
            "
            rule hello = HelloNode { tok1 }

            node HelloNode { }
        "
        );

        let res = SyntaxBuilder::new().build(parse_decls(spec_str));

        assert_eq!(Err(SpecErr::MissingDecl("tok1".into())), res);
    }

    #[test]
    fn node_id_ok() {
        let spec_str = indoc!(
            "
           node Binop { }
        "
        );

        let syntax = get_syntax(spec_str);

        assert_eq!(KindId(Id::from_index(4)), syntax.existing_kind_id("Binop"));
    }

    #[test]
    #[should_panic]
    fn node_missing_id() {
        let spec_str = indoc!(
            "
           node Binop { }
        "
        );

        let syntax = get_syntax(spec_str);
        syntax.existing_kind_id("InvalidName");
    }

    #[test]
    #[should_panic]
    fn not_a_node_name() {
        let spec_str = indoc!(
            "
           term BINOP = 'binop'
        "
        );

        let syntax = get_syntax(spec_str);
        syntax.existing_kind_id("BINOP");
    }

    #[test]
    fn term_id_ok() {
        let spec_str = indoc!(
            "
            term FUN = `function`
        "
        );

        let syntax = get_syntax(spec_str);
        assert_eq!(TagId(Id::from_index(4)), syntax.tag_id("FUN"));
    }

    #[test]
    #[should_panic]
    fn term_missing_id() {
        let spec_str = indoc!(
            "
            term FUN = `function`
        "
        );

        let syntax = get_syntax(spec_str);
        syntax.tag_id("InvalidName");
    }

    #[test]
    #[should_panic]
    fn not_a_term_name() {
        let spec_str = indoc!(
            "
           node Binop { }
        "
        );

        let syntax = get_syntax(spec_str);
        syntax.tag_id("Binop");
    }

    #[test]
    fn rule_id_ok() {
        let spec_str = indoc!(
            "
            rule r = Node { `node` }
            node Node { }
        "
        );

        let syntax = get_syntax(spec_str);
        assert_eq!(RuleId(Id::from_index(5)), syntax.rule_id("r"));
    }

    #[test]
    #[should_panic]
    fn rule_missing_id() {
        let spec_str = indoc!(
            "
            term fun = `function`
        "
        );

        let syntax = get_syntax(spec_str);
        syntax.rule_id("InvalidName");
    }

    #[test]
    fn get_rule_id() {
        let spec_str = indoc!(
            "
            rule r = Node { `node` }
            node Node { }
        "
        );

        let syntax = get_syntax(spec_str);
        assert_eq!(Some(RuleId(Id::from_index(5))), syntax.get_rule_id("r"));
    }

    #[test]
    fn get_rule_id_missing() {
        let spec_str = indoc!(
            "
            rule r = Node { `node` }
            node Node { }
        "
        );

        let syntax = get_syntax(spec_str);
        assert_eq!(None, syntax.get_rule_id("non_existing"));
    }

    #[test]
    #[should_panic]
    fn not_a_rule_name() {
        let spec_str = indoc!(
            "
            node Node { }
        "
        );

        let syntax = get_syntax(spec_str);
        syntax.rule_id("Node");
    }

    #[test]
    fn add_inline_regs() {
        let spec_str = indoc!(
            "
            node Node { }
            rule withInlineTerm = Node { `ab*` field@sepBy(',', withInlineTerm) }
        "
        );

        let syntax = get_syntax(spec_str);
        assert!(matches!(syntax.terminal("ab*"), Some(_)));
        assert!(matches!(syntax.terminal(","), Some(_)));
    }

    #[test]
    fn missing_rule_ref() {
        let spec_str = indoc!(
            "
            node A { }

            rule main = A { `a+` } | non_existing_rule
        "
        );

        let spec_res = SyntaxBuilder::new().build(parse_decls(spec_str));

        assert_eq!(
            spec_res,
            Err(SpecErr::MissingDecl("non_existing_rule".into()))
        )
    }

    #[test]
    fn field_position() {
        let spec_str = indoc!(
            "
            node B { }

            node A { 
                field1: B,
                field2: B
            }

            rule b_node = B { 'b' }

            rule main = A { `a+` }
        "
        );

        let syntax = get_syntax(spec_str);

        let a_kind = syntax.existing_kind_id("A");

        let field1_pos = syntax.field_position(a_kind, "field1").unwrap();
        let field2_pos = syntax.field_position(a_kind, "field2").unwrap();

        assert_eq!(FieldPos::from(0), field1_pos);
        assert_eq!(FieldPos::from(1), field2_pos);
    }

    #[test]
    fn trivial_tags_empty() {
        let spec_str = indoc!(
            "
            node B { }
        "
        );

        let syntax = get_syntax(spec_str);

        assert!(syntax.trivial_tags().is_empty());
    }

    #[test]
    fn trivial_tags() {
        let spec_str = indoc!(
            "
            ignore term A = 'a'
            ignore term B = 'b'

            comment term C = 'c'
            comment term D = 'd'
            comment term E = 'e'
        "
        );

        let syntax = get_syntax(spec_str);

        assert_eq!(5, syntax.trivial_tags.len());

        let ignore_names = HashSet::from(["A", "B"]);
        assert_eq!(
            ignore_names,
            syntax
                .ignore_tags()
                .iter()
                .map(|&t| syntax.tag_name(t))
                .collect()
        );

        let comment_names = HashSet::from(["C", "D", "E"]);
        assert_eq!(
            comment_names,
            syntax
                .comment_tags()
                .iter()
                .map(|&t| syntax.tag_name(t))
                .collect()
        )
    }

    pub fn test_syntax() -> Syntax {
        get_syntax("term HELLO = 'hello'")
    }

    pub fn parse_spec(spec: &str) -> Spec {
        Spec::from_decls(Default::default(), parse_decls(spec)).unwrap()
    }

    fn parse_decls(spec: &str) -> Vec<Decl> {
        parse(spec).expect("Invalid spec")
    }

    fn get_syntax(spec: &str) -> Syntax {
        SyntaxBuilder::new()
            .build(parse(spec).expect("could not parse spec"))
            .expect("Invalid syntax spec")
    }
}
