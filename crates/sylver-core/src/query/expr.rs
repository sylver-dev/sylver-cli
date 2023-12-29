use std::{borrow::Cow, cmp::Ordering, collections::VecDeque};

use derivative::Derivative;
use derive_more::From;
use rustc_hash::FxHashSet;
use sylver_dsl::sylq::ExprRegex;
use thiserror::Error;

use crate::{
    core::spec::{KindId, Spec},
    land::Land,
    query::{expr::EvalError::InvalidKind, RawTreeInfoBuilder, SylvaNode, TreeInfoBuilder},
    script::python::PythonScriptEngine,
    semantic::names::NamesError,
    tree::{info::TreeInfo, Node, NodeId},
};

#[derive(Debug, Clone)]
pub struct EvalCtx<'v, B: TreeInfoBuilder<'v>> {
    memory: Vec<Value<'v>>,
    spec: &'v Spec,
    info_builder: B, // TODO: get rid of the builder/info abstraction
    land: &'v Land,
    script_engine: PythonScriptEngine,
}

impl<'b> EvalCtx<'b, RawTreeInfoBuilder<'b>> {
    pub fn referenced_decls(
        &mut self,
        node: SylvaNode,
    ) -> Result<Option<Vec<SylvaNode>>, EvalError> {
        let mut scopes = self.land.sylva_scopes_mut(node.sylva);
        scopes
            .referenced_decls(
                node,
                self.land,
                &self.spec.aspects,
                self.info_builder.info_for_node(node),
                self.script_engine,
            )
            .map(|decls| decls.map(|decls| decls.to_vec()))
            .map_err(EvalError::NameRes)
    }
}

impl<'b, B: 'b + TreeInfoBuilder<'b>> EvalCtx<'b, B> {
    pub fn childs(&'_ self, node: SylvaNode) -> Vec<SylvaNode> {
        self.info_builder
            .info_for_node(node)
            .node(node.node)
            .childs
            .iter()
            .map(move |&child_id| node.with_node_id(child_id))
            .collect()
    }

    pub fn parent(&self, node: SylvaNode) -> Option<SylvaNode> {
        self.info(node, TreeInfo::parent)
            .map(|parent| node.with_node_id(parent))
    }

    pub fn previous_sibling(&self, node: SylvaNode) -> Option<SylvaNode> {
        self.info(node, TreeInfo::prev_sibling)
            .map(|prev_sibling| node.with_node_id(prev_sibling))
    }

    pub fn next_sibling(&self, node: SylvaNode) -> Option<SylvaNode> {
        self.info(node, TreeInfo::next_sibling)
            .map(|next_sibling| node.with_node_id(next_sibling))
    }

    pub fn node_text(&self, node: SylvaNode) -> &'b str {
        self.info_builder.info_for_node(node).node_text(node.node)
    }

    pub fn node_field(&self, sylva_node: SylvaNode, field: &str) -> Result<Value<'b>, EvalError> {
        let tree_info = self.info_builder.info_for_node(sylva_node);
        let node = tree_info.node(sylva_node.node);

        let field_pos = self
            .spec
            .syntax
            .field_position(node.kind, field)
            .ok_or_else(|| {
                EvalError::InvalidField(
                    field.to_string(),
                    self.spec.syntax.kind_name(node.kind).to_string(),
                )
            })?;

        let field_node = tree_info
            .field_value(sylva_node.node, field_pos)
            .map(|field_node| sylva_node.with_node_id(field_node));

        Ok(field_node.into())
    }

    fn info<F, O>(&self, node: SylvaNode, accessor: F) -> O
    where
        F: Fn(&B::Tree, NodeId) -> O,
    {
        let info = self.info_builder.info_for_node(node);
        accessor(&info, node.node)
    }

    fn tree_node(&self, node: SylvaNode) -> &Node {
        self.info_builder.info_for_node(node).node(node.node)
    }
}

impl<'b, B: TreeInfoBuilder<'b>> EvalCtx<'b, B> {
    pub fn new(
        spec: &'b Spec,
        info_builder: B,
        land: &'b Land,
        script_engine: PythonScriptEngine,
    ) -> Self {
        EvalCtx {
            spec,
            memory: vec![],
            info_builder,
            land,
            script_engine,
        }
    }

    pub fn push_var(&mut self, var: Value<'b>) {
        self.memory.push(var)
    }

    pub fn pop_var(&mut self) -> Option<Value<'b>> {
        self.memory.pop()
    }
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq, Hash)]
pub enum DepthNodeGeneratorFn {
    Parents,
    Descendants,
    Siblings {
        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        seen: FxHashSet<SylvaNode>,
    },
    PreviousSiblings,
    NextSiblings,
}

impl DepthNodeGeneratorFn {
    pub fn siblings() -> Self {
        DepthNodeGeneratorFn::Siblings {
            seen: FxHashSet::default(),
        }
    }

    pub fn gen_from_current<'b, B: 'b + TreeInfoBuilder<'b>>(
        &mut self,
        ctx: &EvalCtx<'b, B>,
        current: DepthNode,
    ) -> Box<dyn 'b + Iterator<Item = DepthNode>> {
        let make_depth_node = move |node| DepthNode {
            node,
            depth: current.depth + 1,
        };

        match self {
            DepthNodeGeneratorFn::Parents => {
                Box::new(ctx.parent(current.node).map(make_depth_node).into_iter())
            }
            DepthNodeGeneratorFn::Descendants => {
                Box::new(ctx.childs(current.node).into_iter().map(make_depth_node))
            }
            DepthNodeGeneratorFn::PreviousSiblings => Box::new(
                ctx.previous_sibling(current.node)
                    .map(make_depth_node)
                    .into_iter(),
            ),
            DepthNodeGeneratorFn::NextSiblings => Box::new(
                ctx.next_sibling(current.node)
                    .map(make_depth_node)
                    .into_iter(),
            ),
            DepthNodeGeneratorFn::Siblings { seen } => {
                let siblings = ctx
                    .next_sibling(current.node)
                    .into_iter()
                    .chain(ctx.previous_sibling(current.node))
                    .filter(|s| {
                        let is_seen = seen.contains(s);

                        if !is_seen {
                            seen.insert(*s);
                        }

                        !is_seen
                    })
                    .collect::<Vec<_>>();

                Box::new(siblings.into_iter().map(make_depth_node))
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct DepthNode {
    node: SylvaNode,
    depth: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DepthNodeGenerator {
    gen_fn: DepthNodeGeneratorFn,
    min_depth: Option<usize>,
    max_depth: Option<usize>,
    next: VecDeque<DepthNode>,
}

impl DepthNodeGenerator {
    fn iter(&self) -> DepthNodeGeneratorIter {
        DepthNodeGeneratorIter { gen: self.clone() }
    }
}

struct DepthNodeGeneratorIter {
    gen: DepthNodeGenerator,
}

trait EvalIterator<'b, B: 'b + TreeInfoBuilder<'b>> {
    type Item;

    fn next_value(&mut self, ctx: &EvalCtx<'b, B>) -> Option<Self::Item>;

    fn count(&mut self, ctx: &EvalCtx<'b, B>) -> usize {
        let mut count = 0;
        while self.next_value(ctx).is_some() {
            count += 1;
        }
        count
    }
}

impl<'b, B: 'b + TreeInfoBuilder<'b>> EvalIterator<'b, B> for DepthNodeGeneratorIter {
    type Item = Value<'b>;

    fn next_value(&mut self, ctx: &EvalCtx<'b, B>) -> Option<Self::Item> {
        let current = self.gen.next.pop_front()?;

        if let Some(max) = self.gen.max_depth {
            if current.depth > max {
                return None;
            }
        }

        for upcoming in self.gen.gen_fn.gen_from_current(ctx, current) {
            self.gen.next.push_back(upcoming);
        }

        if let Some(min) = self.gen.min_depth {
            if current.depth < min {
                return self.next_value(ctx);
            }
        }

        Some(Value::Node(current.node))
    }
}

impl<'b, B: 'b + TreeInfoBuilder<'b>, I: Iterator<Item = Value<'b>>> EvalIterator<'b, B> for I {
    type Item = Value<'b>;

    fn next_value(&mut self, _ctx: &EvalCtx<'b, B>) -> Option<Self::Item> {
        self.next()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, From)]
pub enum Value<'t> {
    Node(SylvaNode),
    Bool(bool),
    Int(i64),
    Kind(KindId),
    String(Cow<'t, str>),
    List(Vec<Value<'t>>),
    Generator(DepthNodeGenerator),
    Null,
}

impl<'t> Value<'t> {
    pub fn kind(&self) -> ValueKind {
        match self {
            Value::Node(_) => ValueKind::Node,
            Value::Bool(_) => ValueKind::Bool,
            Value::String(_) => ValueKind::String,
            Value::Kind(_) => ValueKind::Kind,
            Value::Int(_) => ValueKind::Int,
            Value::List(_) | Value::Generator(_) => ValueKind::List,
            Value::Null => ValueKind::Null,
        }
    }

    pub fn to_static(&self) -> Value<'static> {
        match self {
            Value::String(s) => Value::String(Cow::Owned(s.to_string())),
            Value::Node(n) => Value::Node(*n),
            Value::Bool(b) => Value::Bool(*b),
            Value::Int(i) => Value::Int(*i),
            Value::Kind(k) => Value::Kind(*k),
            Value::List(l) => Value::List(l.iter().map(|v| v.to_static()).collect()),
            Value::Generator(g) => Value::Generator(g.clone()),
            Value::Null => Value::Null,
        }
    }

    fn try_get_children<'c, 'b>(
        self,
        ctx: &'c EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    ) -> Result<Box<dyn 'b + EvalIterator<'b, RawTreeInfoBuilder<'b>, Item = Value<'b>>>, EvalError>
    where
        't: 'b,
    {
        let res = match self {
            Value::List(vs) => Box::new(vs.into_iter())
                as Box<dyn EvalIterator<'b, RawTreeInfoBuilder<'b>, Item = Value<'b>>>,
            Value::Node(n) => Box::new(node_childs_if_list(ctx, n)?.into_iter().map(Into::into)),
            Value::Generator(g) => Box::new(g.iter()),
            _ => return Err(EvalError::InvalidKind(vec![ValueKind::List], self.kind())),
        };

        Ok(res)
    }

    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }
}

impl<'t, T: Into<Value<'t>>> From<Option<T>> for Value<'t> {
    fn from(val: Option<T>) -> Self {
        match val {
            Some(x) => x.into(),
            None => Value::Null,
        }
    }
}

impl<'t> TryInto<SylvaNode> for Value<'t> {
    type Error = EvalError;

    fn try_into(self) -> Result<SylvaNode, Self::Error> {
        match self {
            Value::Node(s) => Ok(s),
            _ => Err(EvalError::InvalidKind(vec![ValueKind::Node], self.kind())),
        }
    }
}

impl<'t> TryInto<bool> for Value<'t> {
    type Error = EvalError;

    fn try_into(self) -> Result<bool, Self::Error> {
        match self {
            Value::Bool(b) => Ok(b),
            _ => Err(EvalError::InvalidKind(vec![ValueKind::Bool], self.kind())),
        }
    }
}

impl<'t> TryInto<Cow<'t, str>> for Value<'t> {
    type Error = EvalError;

    fn try_into(self) -> Result<Cow<'t, str>, Self::Error> {
        match self {
            Value::String(c) => Ok(c),
            _ => Err(EvalError::InvalidKind(vec![ValueKind::String], self.kind())),
        }
    }
}

impl<'t> TryInto<i64> for Value<'t> {
    type Error = EvalError;

    fn try_into(self) -> Result<i64, Self::Error> {
        match self {
            Value::Int(i) => Ok(i),
            _ => Err(EvalError::InvalidKind(vec![ValueKind::Int], self.kind())),
        }
    }
}

impl<'t> TryInto<Vec<Value<'t>>> for Value<'t> {
    type Error = EvalError;

    fn try_into(self) -> Result<Vec<Value<'t>>, Self::Error> {
        match self {
            Value::List(values) => Ok(values),
            _ => Err(EvalError::InvalidKind(vec![ValueKind::List], self.kind())),
        }
    }
}

impl<'t> PartialOrd for Value<'t> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Value::String(s1), Value::String(s2)) => s1.partial_cmp(s2),
            (Value::Int(i1), Value::Int(i2)) => i1.partial_cmp(i2),
            (k1, k2) => panic!("Cannot compare values of kind {k1:?} and {k2:?}"),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, From)]
pub enum ValueKind {
    Node,
    Bool,
    Int,
    Kind,
    String,
    List,
    Null,
}

#[derive(Error, Debug, Eq, PartialEq, Clone, Hash)]
pub enum EvalError {
    #[error("Invalid kind: {1:?}, expected: {0:?}")]
    InvalidKind(Vec<ValueKind>, ValueKind),
    #[error("Invalid memory address: {0}")]
    InvalidAddress(usize),
    #[error("No field: {0} on nodes of kind {1}")]
    InvalidField(String, String),
    #[error("Invalid array index: {0}")]
    IndexError(i64),
    #[error("{0} is not a valid integer")]
    NotAnInt(String),
    #[error("name resolution error: {0}")]
    NameRes(NamesError),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Expr {
    IntConv(Box<Expr>),
    KindAccess(Box<Expr>),
    Const(Value<'static>),
    NodeText(Box<Expr>),
    NodeParent(Box<Expr>),
    NodeChildren(Box<Expr>),
    NodePrevSibling(Box<Expr>),
    NodeNextSibling(Box<Expr>),
    ReferencedDecl(Box<Expr>),
    // TODO: useless with `Not` Expr ?
    NonNullCheck(Box<Expr>),
    Length(Box<Expr>),
    InContext(Vec<Expr>, Box<Expr>),
    ReadVar(usize),
    PropAccess(Box<Expr>, String),
    ArrayIndex(Box<Expr>, Box<Expr>),
    CountCheckMin(Box<Expr>, Box<Expr>, Box<Expr>),
    CountCheckMax(Box<Expr>, Box<Expr>, Box<Expr>),
    // (min-count, origin, predicate)
    RegexMatch(Box<Expr>, ExprRegex),
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    Lte(Box<Expr>, Box<Expr>),
    Ht(Box<Expr>, Box<Expr>),
    Hte(Box<Expr>, Box<Expr>),
    EqEq(Box<Expr>, Box<Expr>),
    Neq(Box<Expr>, Box<Expr>),
    BuildGen(
        Box<Expr>,
        (Option<usize>, Option<usize>),
        DepthNodeGeneratorFn,
    ),
}

impl Expr {
    pub fn int_conv(operand: Expr) -> Expr {
        Expr::unary(Expr::IntConv, operand)
    }

    pub fn kind_access(operand: Expr) -> Expr {
        Expr::unary(Expr::KindAccess, operand)
    }

    pub fn const_expr(value: Value<'static>) -> Expr {
        Expr::Const(value)
    }

    pub fn node_text(operand: Expr) -> Expr {
        Expr::unary(Expr::NodeText, operand)
    }

    pub fn node_parent(operand: Expr) -> Expr {
        Expr::unary(Expr::NodeParent, operand)
    }

    pub fn node_children(operand: Expr) -> Expr {
        Expr::unary(Expr::NodeChildren, operand)
    }

    pub fn node_prev_sibling(operand: Expr) -> Expr {
        Expr::unary(Expr::NodePrevSibling, operand)
    }

    pub fn node_next_sibling(operand: Expr) -> Expr {
        Expr::unary(Expr::NodeNextSibling, operand)
    }

    pub fn referenced_decl(operand: Expr) -> Expr {
        Expr::unary(Expr::ReferencedDecl, operand)
    }

    pub fn non_null_check(operand: Expr) -> Expr {
        Expr::unary(Expr::NonNullCheck, operand)
    }

    pub fn length(operand: Expr) -> Expr {
        Expr::unary(Expr::Length, operand)
    }

    pub fn not_expr(operand: Expr) -> Expr {
        Expr::unary(Expr::Not, operand)
    }

    pub fn in_context(context_values: Vec<Expr>, expr: Expr) -> Expr {
        Expr::InContext(context_values, Box::new(expr))
    }

    pub fn and(left: Expr, right: Expr) -> Expr {
        Expr::binary(Expr::And, left, right)
    }

    pub fn or(left: Expr, right: Expr) -> Expr {
        Expr::binary(Expr::Or, left, right)
    }

    pub fn lt(left: Expr, right: Expr) -> Expr {
        Expr::binary(Expr::Lt, left, right)
    }

    pub fn lte(left: Expr, right: Expr) -> Expr {
        Expr::binary(Expr::Lte, left, right)
    }

    pub fn ht(left: Expr, right: Expr) -> Expr {
        Expr::binary(Expr::Ht, left, right)
    }

    pub fn hte(left: Expr, right: Expr) -> Expr {
        Expr::binary(Expr::Hte, left, right)
    }

    pub fn eq_eq(left: Expr, right: Expr) -> Expr {
        Expr::binary(Expr::EqEq, left, right)
    }

    pub fn neq(left: Expr, right: Expr) -> Expr {
        Expr::binary(Expr::Neq, left, right)
    }

    fn unary(constructor: impl FnOnce(Box<Expr>) -> Expr, inner: Expr) -> Expr {
        constructor(Box::new(inner))
    }

    fn binary(
        constructor: impl FnOnce(Box<Expr>, Box<Expr>) -> Expr,
        left: Expr,
        right: Expr,
    ) -> Expr {
        constructor(Box::new(left), Box::new(right))
    }

    pub fn read_var(addr: usize) -> Expr {
        Expr::ReadVar(addr)
    }

    pub fn prop_access(operand: Expr, field: String) -> Expr {
        Expr::PropAccess(Box::new(operand), field)
    }

    pub fn array_index(array: Expr, index: Expr) -> Expr {
        Expr::ArrayIndex(Box::new(array), Box::new(index))
    }

    pub fn count_check_min(min_count: Expr, origin: Expr, predicate: Expr) -> Expr {
        Expr::CountCheckMin(Box::new(min_count), Box::new(origin), Box::new(predicate))
    }

    pub fn count_check_max(max_count: Expr, origin: Expr, predicate: Expr) -> Expr {
        Expr::CountCheckMax(Box::new(max_count), Box::new(origin), Box::new(predicate))
    }

    pub fn regex_match(operand: Expr, regex: ExprRegex) -> Expr {
        Expr::RegexMatch(Box::new(operand), regex)
    }

    pub fn ternary(condition: Expr, consequence: Expr, alternative: Expr) -> Expr {
        Expr::Ternary(
            Box::new(condition),
            Box::new(consequence),
            Box::new(alternative),
        )
    }

    pub fn build_gen(
        operand: Expr,
        depths: (Option<usize>, Option<usize>),
        gen_fn: DepthNodeGeneratorFn,
    ) -> Expr {
        Expr::BuildGen(Box::new(operand), depths, gen_fn)
    }

    pub fn eval<'b>(
        &self,
        ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    ) -> Result<Value<'b>, EvalError> {
        match self {
            Expr::IntConv(e) => eval_int_conv(ctx, e),
            Expr::KindAccess(op) => eval_kind_access(ctx, op),
            Expr::Const(v) => Ok(v.clone()),
            Expr::NodeText(o) => eval_node_text(ctx, o),
            Expr::NodeParent(n) => eval_node_parent(ctx, n),
            Expr::NodeChildren(n) => eval_node_children(ctx, n),
            Expr::NodePrevSibling(n) => eval_node_prev_sibling(ctx, n),
            Expr::NodeNextSibling(n) => eval_node_next_sibling(ctx, n),
            Expr::ReferencedDecl(n) => eval_referenced_decl(ctx, n),
            Expr::Length(o) => eval_length(ctx, o),
            Expr::InContext(ctx_values, e) => eval_in_context(ctx, ctx_values, e),
            Expr::ReadVar(addr) => eval_read_var(ctx, *addr),
            Expr::PropAccess(o, p) => eval_prop_access(ctx, o, p),
            Expr::ArrayIndex(array, index) => eval_array_index(ctx, array, index),
            Expr::CountCheckMin(min_count, source, predicate) => eval_count_check(
                ctx,
                |current, min| current < min,
                min_count,
                source,
                predicate,
            ),
            Expr::CountCheckMax(max_count, source, predicate) => eval_count_check(
                ctx,
                |current, max| current <= max,
                max_count,
                source,
                predicate,
            ),
            Expr::RegexMatch(e, r) => eval_regex_match(ctx, e, r),
            Expr::Ternary(cond, cons, alt) => eval_ternary(ctx, cond, cons, alt),
            Expr::NonNullCheck(e) => {
                let is_null = e.eval(ctx)?.is_null();
                Ok((!is_null).into())
            }
            Expr::And(l, r) => Ok(Value::Bool(
                l.eval(ctx)?.try_into()? && r.eval(ctx)?.try_into()?,
            )),
            Expr::Or(l, r) => Ok(Value::Bool(
                l.eval(ctx)?.try_into()? || r.eval(ctx)?.try_into()?,
            )),
            Expr::Lt(l, r) => Ok(Value::Bool(l.eval(ctx)? < r.eval(ctx)?)),
            Expr::Lte(l, r) => Ok(Value::Bool(l.eval(ctx)? <= r.eval(ctx)?)),
            Expr::Ht(l, r) => Ok(Value::Bool(l.eval(ctx)? > r.eval(ctx)?)),
            Expr::Hte(l, r) => Ok(Value::Bool(l.eval(ctx)? >= r.eval(ctx)?)),
            Expr::EqEq(l, r) => eval_eq_eq(ctx, l, r),
            Expr::Neq(l, r) => eval_neq(ctx, l, r),
            Expr::Not(operand) => {
                let operand_val: bool = operand.eval(ctx)?.try_into()?;
                Ok((!operand_val).into())
            }
            Expr::BuildGen(operand, depts, gen_fn) => eval_build_gen(ctx, operand, depts, gen_fn),
        }
    }
}

fn eval_build_gen<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    operand: &Expr,
    (min_depth, matx_depth): &(Option<usize>, Option<usize>),
    gen_fn: &DepthNodeGeneratorFn,
) -> Result<Value<'b>, EvalError> {
    let node: SylvaNode = operand.eval(ctx)?.try_into()?;
    let mut gen_fn = gen_fn.clone();
    let init_next = VecDeque::from_iter(gen_fn.gen_from_current(ctx, DepthNode { depth: 0, node }));
    Ok(Value::Generator(DepthNodeGenerator {
        gen_fn,
        min_depth: *min_depth,
        max_depth: *matx_depth,
        next: init_next,
    }))
}

fn eval_neq<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    left: &Expr,
    right: &Expr,
) -> Result<Value<'b>, EvalError> {
    let left_val = left.eval(ctx)?;
    let right_val = right.eval(ctx)?;

    let not_equals = match (left_val.kind(), right_val.kind()) {
        (ValueKind::Node, ValueKind::String) => node_value_text(ctx, left_val)? != right_val,
        (ValueKind::String, ValueKind::Node) => left_val != node_value_text(ctx, right_val)?,
        _ => left_val != right_val,
    };

    Ok(not_equals.into())
}

fn eval_eq_eq<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    left: &Expr,
    right: &Expr,
) -> Result<Value<'b>, EvalError> {
    let left_val = left.eval(ctx)?;
    let right_val = right.eval(ctx)?;

    if left_val == right_val {
        return Ok(true.into());
    }

    let equals = match (left_val.kind(), right_val.kind()) {
        (ValueKind::Node, ValueKind::String) => node_value_text(ctx, left_val)? == right_val,
        (ValueKind::String, ValueKind::Node) => left_val == node_value_text(ctx, right_val)?,
        _ => false,
    };

    Ok(equals.into())
}

fn eval_int_conv<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    expr: &Expr,
) -> Result<Value<'b>, EvalError> {
    let value = expr.eval(ctx)?;

    let integer = match value {
        Value::Int(i) => i,
        Value::String(s) => s
            .parse()
            .map_err(|_| EvalError::NotAnInt(format!("\"{s}\"")))?,
        _ => {
            return Err(EvalError::InvalidKind(
                vec![ValueKind::Int, ValueKind::String],
                value.kind(),
            ));
        }
    };

    Ok(Value::Int(integer))
}

fn eval_kind_access<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    op: &Expr,
) -> Result<Value<'b>, EvalError> {
    let sylva_node: SylvaNode = op.eval(ctx)?.try_into()?;
    let kind = ctx
        .info_builder
        .info_for_node(sylva_node)
        .node(sylva_node.node)
        .kind;
    Ok(Value::Kind(kind))
}

fn eval_node_text<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    op: &Expr,
) -> Result<Value<'b>, EvalError> {
    let node_val = op.eval(ctx)?;
    node_value_text(ctx, node_val)
}

fn node_value_text<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    value: Value<'b>,
) -> Result<Value<'b>, EvalError> {
    let sylva_node: SylvaNode = value.try_into()?;
    let text = ctx.node_text(sylva_node);
    Ok(Value::String(Cow::Borrowed(text)))
}

fn eval_node_parent<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    op: &Expr,
) -> Result<Value<'b>, EvalError> {
    let sylva_node: SylvaNode = op.eval(ctx)?.try_into()?;
    let parent = ctx.parent(sylva_node);
    Ok(parent.into())
}

fn eval_node_children<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    op: &Expr,
) -> Result<Value<'b>, EvalError> {
    let sylva_node: SylvaNode = op.eval(ctx)?.try_into()?;
    let childs = ctx.childs(sylva_node).into_iter().map(Into::into).collect();
    Ok(Value::List(childs))
}

fn eval_node_prev_sibling<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    op: &Expr,
) -> Result<Value<'b>, EvalError> {
    let sylva_node = op.eval(ctx)?.try_into()?;
    Ok(ctx.previous_sibling(sylva_node).into())
}

fn eval_node_next_sibling<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    op: &Expr,
) -> Result<Value<'b>, EvalError> {
    let sylva_node = op.eval(ctx)?.try_into()?;
    Ok(ctx.next_sibling(sylva_node).into())
}

fn eval_referenced_decl<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    op: &Expr,
) -> Result<Value<'b>, EvalError> {
    let sylva_node: SylvaNode = op.eval(ctx)?.try_into()?;

    let decls = ctx.referenced_decls(sylva_node);

    decls.map(|decls| {
        decls
            .map(|decls| Value::List(decls.into_iter().map(Into::into).collect()))
            .unwrap_or(Value::Null)
    })
}

fn eval_length<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    op: &Expr,
) -> Result<Value<'b>, EvalError> {
    let value_len = match op.eval(ctx)? {
        Value::String(s) => s.len(),
        Value::List(l) => l.len(),
        Value::Node(n) => node_childs_if_list(ctx, n)?.len(),
        Value::Generator(g) => g.iter().count(ctx),
        _ => {
            return Err(EvalError::InvalidKind(
                vec![ValueKind::String, ValueKind::List],
                ValueKind::Node,
            ));
        }
    };

    Ok(Value::Int(value_len as i64))
}

fn eval_in_context<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    ctx_exprs: &[Expr],
    expr: &Expr,
) -> Result<Value<'b>, EvalError> {
    for ctx_expr in ctx_exprs {
        let ctx_val = ctx_expr.eval(ctx)?;
        ctx.push_var(ctx_val);
    }

    let result_value = expr.eval(ctx)?;

    for _ in 0..ctx_exprs.len() {
        ctx.pop_var();
    }

    Ok(result_value)
}

fn eval_read_var<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    addr: usize,
) -> Result<Value<'b>, EvalError> {
    ctx.memory
        .get(addr)
        .cloned()
        .ok_or(EvalError::InvalidAddress(addr))
}

fn eval_prop_access<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    operand: &Expr,
    prop: &str,
) -> Result<Value<'b>, EvalError> {
    let sylva_node: SylvaNode = operand.eval(ctx)?.try_into()?;
    ctx.node_field(sylva_node, prop)
}

fn eval_array_index<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    array: &Expr,
    index: &Expr,
) -> Result<Value<'b>, EvalError> {
    let index: i64 = index.eval(ctx)?.try_into()?;

    if index < 0 {
        return Err(EvalError::IndexError(index));
    }

    let val_at_index = match array.eval(ctx)? {
        Value::List(vals) => vals.get(index as usize).cloned(),
        Value::Node(n) => ctx.childs(n).get(index as usize).copied().map(Into::into),
        _ => None,
    };

    val_at_index.ok_or(EvalError::IndexError(index))
}

fn eval_count_check<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    continue_condition: impl Fn(i64, i64) -> bool,
    target_count: &Expr,
    source: &Expr,
    predicate: &Expr,
) -> Result<Value<'b>, EvalError> {
    let target_count: i64 = target_count.eval(ctx)?.try_into()?;
    let mut nodes = source.eval(ctx)?.try_get_children(ctx)?;

    let mut current_count = 0;

    while let Some(n) = nodes.next_value(ctx) {
        if !continue_condition(current_count, target_count) {
            break;
        }

        ctx.push_var(n);
        let predicate_value: bool = predicate.eval(ctx)?.try_into()?;
        ctx.pop_var();

        if predicate_value {
            current_count += 1;
        }
    }

    Ok((current_count == target_count).into())
}

fn eval_regex_match<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    expr: &Expr,
    regex: &ExprRegex,
) -> Result<Value<'b>, EvalError> {
    let expr_result: Cow<'b, str> = expr.eval(ctx)?.try_into()?;
    Ok(regex.is_match(expr_result.as_ref()).into())
}

fn eval_ternary<'b>(
    ctx: &mut EvalCtx<'b, RawTreeInfoBuilder<'b>>,
    condition: &Expr,
    consequence: &Expr,
    alternative: &Expr,
) -> Result<Value<'b>, EvalError> {
    let condition: bool = condition.eval(ctx)?.try_into()?;

    if condition {
        consequence.eval(ctx)
    } else {
        alternative.eval(ctx)
    }
}

fn node_childs_if_list<'b, B: 'b + TreeInfoBuilder<'b>>(
    ctx: &EvalCtx<'b, B>,
    n: SylvaNode,
) -> Result<Vec<SylvaNode>, EvalError> {
    let node = ctx.tree_node(n);

    if ctx.spec.syntax.is_list_kind(node.kind) {
        Ok(ctx.childs(n))
    } else {
        Err(InvalidKind(vec![ValueKind::List], ValueKind::Node))
    }
}

#[cfg(test)]
pub mod test {
    use std::collections::HashMap;

    use crate::{
        land::{builder::LandBuilder, sylva::Sylva},
        parsing::sppf::Span,
        query::test::TestTreeInfoBuilder,
        tree::{info::tests::TestTreeInfo, Node},
    };

    use super::*;

    #[test]
    fn regex_match_ok() {
        let expr = Expr::regex_match(
            Expr::Const(Value::String("hello".into())),
            fancy_regex::Regex::new("hello").unwrap().into(),
        );

        assert_eq!(Ok(true.into()), eval_in_default_ctx(expr));
    }

    #[test]
    fn regex_match_notok() {
        let expr = Expr::regex_match(
            Expr::Const(Value::String("hello".into())),
            fancy_regex::Regex::new("world").unwrap().into(),
        );

        assert_eq!(Ok(false.into()), eval_in_default_ctx(expr));
    }

    #[test]
    fn ternary_true() {
        let expr = Expr::ternary(
            Expr::const_expr(true.into()),
            Expr::const_expr(1.into()),
            Expr::const_expr(0.into()),
        );

        assert_eq!(Ok(1.into()), eval_in_default_ctx(expr));
    }

    #[test]
    fn ternary_false() {
        let expr = Expr::ternary(
            Expr::const_expr(false.into()),
            Expr::const_expr(1.into()),
            Expr::const_expr(0.into()),
        );

        assert_eq!(Ok(0.into()), eval_in_default_ctx(expr));
    }

    #[test]
    fn non_null_ok() {
        let expr = Expr::non_null_check(Expr::const_expr(true.into()));
        assert_eq!(Ok(true.into()), eval_in_default_ctx(expr));
    }

    #[test]
    fn non_null_notok() {
        let expr = Expr::non_null_check(Expr::const_expr(Value::Null));
        assert_eq!(Ok(false.into()), eval_in_default_ctx(expr));
    }

    #[test]
    fn const_expr() {
        let expr = Expr::Const(Value::Bool(true));
        assert_eq!(Ok(Value::Bool(true)), eval_in_default_ctx(expr));
    }

    #[test]
    fn string_length() {
        let expr = Expr::length(Expr::Const(Value::String("hello".into())));
        assert_eq!(Ok(Value::Int(5)), eval_in_default_ctx(expr));
    }

    #[test]
    fn list_length() {
        let expr = Expr::length(Expr::Const(Value::List(vec![0.into(), 1.into(), 2.into()])));
        assert_eq!(Ok(Value::Int(3)), eval_in_default_ctx(expr));
    }

    #[test]
    fn int_conv_from_int() {
        let expr = Expr::int_conv(Expr::const_expr(42.into()));
        assert_eq!(Ok(Value::Int(42)), eval_in_default_ctx(expr));
    }

    #[test]
    fn int_conv_from_positive_string() {
        let expr = Expr::int_conv(Expr::const_expr(Value::String(Cow::Borrowed("43"))));
        assert_eq!(Ok(Value::Int(43)), eval_in_default_ctx(expr));
    }

    #[test]
    fn int_conv_from_negative_string() {
        let expr = Expr::int_conv(Expr::const_expr(Value::String(Cow::Borrowed("-43"))));
        assert_eq!(Ok(Value::Int(-43)), eval_in_default_ctx(expr));
    }

    #[test]
    fn int_conv_from_nonint_string() {
        let expr = Expr::int_conv(Expr::const_expr(Value::String(Cow::Borrowed("hello"))));
        assert_eq!(
            Err(EvalError::NotAnInt(r#""hello""#.to_string())),
            eval_in_default_ctx(expr)
        );
    }

    #[test]
    fn int_conv_from_bool() {
        let expr = Expr::int_conv(Expr::const_expr(false.into()));
        assert_eq!(
            Err(EvalError::InvalidKind(
                vec![ValueKind::Int, ValueKind::String],
                ValueKind::Bool,
            )),
            eval_in_default_ctx(expr)
        );
    }

    #[test]
    fn eqeq_operator_ok() {
        assert_eq!(Value::Bool(true), eval_binop(Expr::eq_eq, 10, 10));
    }

    #[test]
    fn eqeq_operator_notok() {
        assert_eq!(Value::Bool(false), eval_binop(Expr::eq_eq, 10, 11));
    }

    #[test]
    fn neq_opeartor_ok() {
        assert_eq!(Value::Bool(true), eval_binop(Expr::neq, 1, 0));
    }

    #[test]
    fn neq_opeartor_notok() {
        assert_eq!(Value::Bool(false), eval_binop(Expr::neq, 1, 1));
    }

    #[test]
    fn lt_operator_int() {
        assert_eq!(Value::Bool(true), eval_binop(Expr::lt, 0, 1),);
    }

    #[test]
    fn lt_operator_int_false() {
        assert_eq!(Value::Bool(false), eval_binop(Expr::lt, 1, 0));
    }

    #[test]
    fn lte_operator_int_less() {
        assert_eq!(Value::Bool(true), eval_binop(Expr::lte, 0, 1));
    }

    #[test]
    fn lte_operator_int_eq() {
        assert_eq!(Value::Bool(true), eval_binop(Expr::lte, 1, 1));
    }

    #[test]
    fn lte_operator_int_false() {
        assert_eq!(Value::Bool(false), eval_binop(Expr::lte, 1, 0));
    }

    #[test]
    fn ht_operator_int() {
        assert_eq!(Value::Bool(true), eval_binop(Expr::ht, 1, 0));
    }

    #[test]
    fn ht_operator_int_false() {
        assert_eq!(Value::Bool(false), eval_binop(Expr::ht, 0, 1));
    }

    #[test]
    fn hte_operator_int_true() {
        assert_eq!(Value::Bool(true), eval_binop(Expr::hte, 1, 0));
    }

    #[test]
    fn hte_operator_int_eq() {
        assert_eq!(Value::Bool(true), eval_binop(Expr::hte, 1, 1));
    }

    #[test]
    fn hte_operator_int_false() {
        assert_eq!(Value::Bool(false), eval_binop(Expr::hte, 0, 1));
    }

    #[test]
    fn and_ok() {
        assert_eq!(Value::Bool(true), eval_binop(Expr::and, true, true));
    }

    #[test]
    fn and_notok() {
        assert_eq!(Value::Bool(false), eval_binop(Expr::and, false, true));

        assert_eq!(Value::Bool(false), eval_binop(Expr::and, true, false));

        assert_eq!(Value::Bool(false), eval_binop(Expr::and, false, false));
    }

    #[test]
    fn or_ok() {
        assert_eq!(Value::Bool(true), eval_binop(Expr::or, false, true));

        assert_eq!(Value::Bool(true), eval_binop(Expr::or, true, false));

        assert_eq!(Value::Bool(true), eval_binop(Expr::or, true, true));
    }

    #[test]
    fn or_notok() {
        assert_eq!(Value::Bool(false), eval_binop(Expr::or, false, false));
    }

    #[test]
    fn read_var() {
        let value = Value::Int(42);

        let expr = Expr::in_context(vec![Expr::const_expr(value.clone())], Expr::read_var(0));

        assert_eq!(Ok(Value::Int(42)), eval_in_default_ctx(expr));
    }

    #[test]
    fn read_invalid_var() {
        let expr = Expr::read_var(1);

        assert_eq!(Err(EvalError::InvalidAddress(1)), eval_in_default_ctx(expr));
    }

    #[test]
    fn kind_access() {
        let kind = 1.into();

        let node = Node {
            kind,
            span: Span::new(0, 1),
            parent: None,
            named_childs: vec![],
            childs: vec![],
        };

        let expr = Expr::kind_access(Expr::read_var(0));

        run_on_node(node, expr, Ok(Value::Kind(kind)));
    }

    fn eval_binop(
        binop: impl Fn(Expr, Expr) -> Expr,
        left: impl Into<Value<'static>>,
        right: impl Into<Value<'static>>,
    ) -> Value<'static> {
        let prepared_expr = Expr::in_context(
            vec![Expr::Const(left.into()), Expr::Const(right.into())],
            binop(Expr::read_var(0), Expr::read_var(1)),
        );

        eval_in_default_ctx(prepared_expr).unwrap()
    }

    fn run_on_node(node: Node, expr: Expr, expected_res: Result<Value, EvalError>) {
        let mut nodes = HashMap::new();
        let mut nodes_code = HashMap::new();
        let tree_info = build_test_tree_info(vec![node], &mut nodes, &mut nodes_code);

        let mut builder = TestTreeInfoBuilder::default();

        let sylva_node = SylvaNode {
            node: 0.into(),
            sylva: 0.into(),
            tree: 0.into(),
        };

        builder.infos.insert(sylva_node, tree_info);

        let spec = Spec::from_decls(Default::default(), vec![]).unwrap();

        let sylva = Sylva::new(HashMap::new());
        let land = LandBuilder::default().build();
        let mut ctx = EvalCtx::new(
            &spec,
            RawTreeInfoBuilder::new(&spec, &sylva),
            &land,
            PythonScriptEngine::default(),
        );
        ctx.push_var(Value::Node(sylva_node));

        assert_eq!(expected_res, expr.eval(&mut ctx))
    }

    fn eval_in_default_ctx(expr: Expr) -> Result<Value<'static>, EvalError> {
        let spec = Spec::from_decls(Default::default(), vec![]).unwrap();
        let sylva = Sylva::new(HashMap::new());
        let land = LandBuilder::default().build();
        let mut ctx = EvalCtx::new(
            &spec,
            RawTreeInfoBuilder::new(&spec, &sylva),
            &land,
            PythonScriptEngine::default(),
        );

        expr.eval(&mut ctx).map(|val| val.to_static())
    }

    pub fn build_test_tree_info<'t>(
        nodes: Vec<Node>,
        nodes_map: &'t mut HashMap<NodeId, Node>,
        nodes_code: &'t mut HashMap<NodeId, String>,
    ) -> TestTreeInfo<'t> {
        if nodes.is_empty() {
            panic!("Cannot build a test tree without nodes");
        }

        *nodes_map = nodes
            .into_iter()
            .enumerate()
            .map(|(i, n)| (i.into(), n))
            .collect();

        TestTreeInfo::new(nodes_map, nodes_code, 0.into())
    }
}
