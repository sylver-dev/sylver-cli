use std::{borrow::Cow, collections::HashMap};

use itertools::Itertools;
use thiserror::Error;

use sylver_dsl::sylq::{
    ArrayQuantQuant, Expr as SyntaxExpr, KindPattern, NodePattern, NodePatternField,
    NodePatternFieldValue, Op, QueryPattern,
};

use crate::{
    core::spec::{strip_list_kind, KindId, Spec},
    query::expr::{Expr, Value},
};

pub const DEFAULT_INPUT_ADDR: usize = 0;

#[derive(Debug, Eq, PartialEq, Error)]
pub enum CompilationErr {
    #[error("Invalid kind name: {0}")]
    InvalidKind(String),
    #[error("Unknown identifier: {0}")]
    UnknownIdentifier(String),
    #[error("Invalid property name: {0}")]
    InvalidPropertyName(String),
    #[error("Missing arg for method {0}. Arity is {1}")]
    UnexpectedArity(String, usize),
    #[error("Unexpected arg for method {0}. Expected {1}.")]
    UnexpectedArg(String, String),
}

struct Compiler<'s> {
    spec: &'s Spec,
    bindings: HashMap<String, usize>,
    reserved_vars: usize,
}

impl<'s> Compiler<'s> {
    fn for_spec(spec: &'s Spec) -> Compiler<'s> {
        Compiler {
            spec,
            bindings: HashMap::new(),
            reserved_vars: 1, // Address 0 is reserved to the input
        }
    }

    fn compile(&mut self, query: &QueryPattern) -> Result<Expr, CompilationErr> {
        let filter_expr = self.compile_query_pattern(DEFAULT_INPUT_ADDR, query)?;
        Ok(filter_expr)
    }

    fn compile_query_pattern(
        &mut self,
        operand_addr: usize,
        pattern: &QueryPattern,
    ) -> Result<Expr, CompilationErr> {
        let pattern_expr = self.pattern(operand_addr, &pattern.node_pattern)?;

        let predicate_expr = pattern
            .predicate
            .as_ref()
            .map(|p| self.expr(p))
            .transpose()?;

        let complete_expr = if let Some(predicate) = predicate_expr {
            Expr::and(pattern_expr, predicate)
        } else {
            pattern_expr
        };

        Ok(complete_expr)
    }

    fn pattern(
        &mut self,
        operand_addr: usize,
        pattern: &NodePattern,
    ) -> Result<Expr, CompilationErr> {
        if let Some(b) = &pattern.binding {
            self.bindings.insert(b.to_string(), operand_addr);
        }

        let operand_expr = Expr::read_var(operand_addr);

        let kind = self.kind_constraint(operand_expr.clone(), &pattern.kind_pattern)?;

        let mut fields = pattern
            .fields
            .iter()
            .map(|f| self.field_check(operand_expr.clone(), f));

        fields.fold_ok(kind, Expr::and)
    }

    fn field_check(
        &mut self,
        operand: Expr,
        field: &NodePatternField,
    ) -> Result<Expr, CompilationErr> {
        let field_expr = Expr::prop_access(operand, field.name.clone());

        let field_predicate = match &field.value {
            NodePatternFieldValue::Text(t) => Expr::eq_eq(
                field_expr,
                Expr::const_expr(Value::String(Cow::Owned(t.to_string()))),
            ),
            NodePatternFieldValue::Pattern(p) => {
                self.with_value(field_expr, |compiler, value_adr| {
                    let field_pattern_expr = compiler.compile_query_pattern(value_adr, p)?;
                    Ok(Expr::and(
                        Expr::neq(Expr::read_var(value_adr), Expr::const_expr(Value::Null)),
                        field_pattern_expr,
                    ))
                })?
            }
        };

        Ok(field_predicate)
    }

    fn expr(&mut self, expr: &SyntaxExpr) -> Result<Expr, CompilationErr> {
        match expr {
            SyntaxExpr::Identifier(i) => self
                .bindings
                .get(i)
                .map(|&addr| Ok(Expr::read_var(addr)))
                .unwrap_or_else(|| Err(CompilationErr::UnknownIdentifier(i.clone()))),
            SyntaxExpr::Integer(i) => Ok(Expr::Const(Value::Int(*i))),
            SyntaxExpr::Null => Ok(Expr::const_expr(Value::Null)),
            SyntaxExpr::StringLit(s) => {
                Ok(Expr::const_expr(Value::String(Cow::Owned(s.to_string()))))
            }
            SyntaxExpr::DotAccess(safe, op, p) => self.dot_access(*safe, op, p),
            SyntaxExpr::DotCall(safe, op, callee, args) => self.dot_call(*safe, op, callee, args),
            SyntaxExpr::Not(e) => Ok(Expr::not_expr(self.expr(e)?)),
            SyntaxExpr::Binop(l, o, r) => {
                let left = self.expr(l)?;
                let right = self.expr(r)?;
                Ok(match o {
                    Op::Lt => Expr::lt(left, right),
                    Op::Lte => Expr::lte(left, right),
                    Op::Ht => Expr::ht(left, right),
                    Op::Hte => Expr::hte(left, right),
                    Op::Or => Expr::or(left, right),
                    Op::And => Expr::and(left, right),
                    Op::EqEq => Expr::eq_eq(left, right),
                    Op::Neq => Expr::neq(left, right),
                })
            }
            SyntaxExpr::Is(operand, pattern) => self.expr_is(operand, pattern),
            SyntaxExpr::ArrayIndex(array, index) => self.array_index(array, index),
            SyntaxExpr::ArrayQuant(min_count, origin, predicate) => {
                self.array_quant(min_count, origin, predicate)
            }
            SyntaxExpr::RegexLit(r) => Ok(Expr::const_expr(Value::String(Cow::Owned(
                r.as_str().to_string(),
            )))),
        }
    }

    fn dot_access(
        &mut self,
        safe: bool,
        expr: &SyntaxExpr,
        prop: &String,
    ) -> Result<Expr, CompilationErr> {
        let operand = self.expr(expr)?;

        let access = match prop.as_str() {
            "text" => Expr::node_text(operand.clone()),
            "length" => Expr::length(operand.clone()),
            "kind" => Expr::kind_access(operand.clone()),
            "parent" => Expr::node_parent(operand.clone()),
            "children" => Expr::node_children(operand.clone()),
            "previous_sibling" => Expr::node_prev_sibling(operand.clone()),
            "next_sibling" => Expr::node_next_sibling(operand.clone()),
            field if self.spec.syntax.field_names().contains(&field) => {
                Expr::prop_access(operand.clone(), field.to_string())
            }
            _ => return Err(CompilationErr::InvalidPropertyName(prop.to_string())),
        };

        Ok(make_safe(safe, operand, access))
    }

    fn dot_call(
        &mut self,
        safe: bool,
        expr: &SyntaxExpr,
        callee: &str,
        args: &[SyntaxExpr],
    ) -> Result<Expr, CompilationErr> {
        let operand = self.expr(expr)?;

        let call_expr = match callee {
            "matches" => {
                if args.len() != 1 {
                    return Err(CompilationErr::UnexpectedArity(
                        callee.to_string(),
                        args.len(),
                    ));
                }

                match &args[0] {
                    SyntaxExpr::RegexLit(r) => Expr::regex_match(operand.clone(), r.clone()),
                    _ => {
                        return Err(CompilationErr::UnexpectedArg(
                            callee.to_string(),
                            "regex".to_string(),
                        ));
                    }
                }
            }
            "to_int" => {
                if !args.is_empty() {
                    return Err(CompilationErr::UnexpectedArity(
                        callee.to_string(),
                        args.len(),
                    ));
                }

                Expr::int_conv(operand.clone())
            }
            _ => return Err(CompilationErr::InvalidPropertyName(callee.to_string())),
        };

        Ok(make_safe(safe, operand, call_expr))
    }

    fn expr_is(
        &mut self,
        operand: &SyntaxExpr,
        pattern: &QueryPattern,
    ) -> Result<Expr, CompilationErr> {
        let compiled_operand = self.expr(operand)?;

        self.with_value(compiled_operand, |compiler, value_addr| {
            let pattern_expr = compiler.compile_query_pattern(value_addr, pattern)?;

            Ok(Expr::and(
                Expr::non_null_check(Expr::read_var(value_addr)),
                pattern_expr,
            ))
        })
    }

    fn array_index(
        &mut self,
        array: &SyntaxExpr,
        index: &SyntaxExpr,
    ) -> Result<Expr, CompilationErr> {
        let compiled_array = self.expr(array)?;
        let compiled_index = self.expr(index)?;
        Ok(Expr::array_index(compiled_array, compiled_index))
    }

    fn array_quant(
        &mut self,
        quant: &ArrayQuantQuant,
        origin: &SyntaxExpr,
        pattern: &QueryPattern,
    ) -> Result<Expr, CompilationErr> {
        let origin = self.expr(origin)?;

        self.with_value(origin, |compiler, origin_addr| {
            let children_addr = compiler.reserve_var();
            let predicate = compiler.compile_query_pattern(children_addr, pattern)?;
            compiler.release_var();

            let origin_expr = Expr::read_var(origin_addr);

            let res = match quant {
                ArrayQuantQuant::No => {
                    Expr::count_check_max(Expr::const_expr(0.into()), origin_expr, predicate)
                }
                ArrayQuantQuant::Any => {
                    Expr::count_check_min(Expr::const_expr(1.into()), origin_expr, predicate)
                }
                ArrayQuantQuant::All => {
                    Expr::count_check_min(Expr::length(origin_expr.clone()), origin_expr, predicate)
                }
            };

            Ok(res)
        })
    }

    fn with_value(
        &mut self,
        value: Expr,
        action: impl FnOnce(&mut Self, usize) -> Result<Expr, CompilationErr>,
    ) -> Result<Expr, CompilationErr> {
        let addr = self.reserve_var();
        let action_result = action(self, addr)?;
        self.release_var();

        Ok(Expr::in_context(vec![value], action_result))
    }

    fn kind_constraint(
        &mut self,
        operand: Expr,
        pattern: &KindPattern,
    ) -> Result<Expr, CompilationErr> {
        match pattern {
            KindPattern::KindName(n) => {
                let kind_id = self.get_kind_id(n)?;
                let first_check = make_kind_check(operand.clone(), kind_id);

                let checks = self
                    .spec
                    .child_kinds(kind_id)
                    .into_iter()
                    .fold(first_check, |acc, child_kind| {
                        Expr::or(acc, make_kind_check(operand.clone(), child_kind))
                    });

                Ok(checks)
            }
            KindPattern::Placeholder => Ok(Expr::const_expr(Value::Bool(true))),
        }
    }

    fn get_kind_id(&self, kind_name: &str) -> Result<KindId, CompilationErr> {
        match self.spec.syntax.kind_id(kind_name) {
            Some(id) => Ok(id),
            None => Err(CompilationErr::InvalidKind(strip_list_kind(kind_name))),
        }
    }

    fn reserve_var(&mut self) -> usize {
        let addr = self.reserved_vars;
        self.reserved_vars += 1;
        addr
    }

    fn release_var(&mut self) {
        self.reserved_vars -= 1;
    }
}

pub fn compile(spec: &Spec, query: &QueryPattern) -> Result<Expr, CompilationErr> {
    Compiler::for_spec(spec).compile(query)
}

fn make_kind_check(operand: Expr, kind: KindId) -> Expr {
    Expr::eq_eq(Expr::kind_access(operand), Expr::const_expr(kind.into()))
}

fn make_safe(safe: bool, operand: Expr, access_expr: Expr) -> Expr {
    if safe {
        Expr::ternary(
            Expr::neq(operand, Expr::Const(Value::Null)),
            access_expr,
            Expr::const_expr(Value::Null),
        )
    } else {
        access_expr
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use sylver_dsl::sylq::{parse_expr, parse_query};

    use crate::core::spec::test::parse_spec;

    use super::*;

    #[test]
    fn compile_regex_conv() {
        let compiled = Compiler::for_spec(&parse_spec("node NodeKind {}"))
            .expr(&parse_expr("'42'.to_int()"))
            .unwrap();

        assert_eq!(
            compiled,
            Expr::int_conv(Expr::const_expr(Value::String(Cow::Borrowed("42"))))
        )
    }

    #[test]
    fn compile_regex_match() {
        let compiled = Compiler::for_spec(&parse_spec("node NodeKind {}"))
            .expr(&parse_expr("'hello'.matches(`[a-z]+`)"))
            .unwrap();

        assert_eq!(
            compiled,
            Expr::regex_match(
                Expr::const_expr(Value::String(Cow::Owned("hello".into()))),
                fancy_regex::Regex::new("[a-z]+").unwrap().into(),
            )
        )
    }

    #[test]
    fn compile_safe_regex_match() {
        let compiled = Compiler::for_spec(&parse_spec("node NodeKind {}"))
            .expr(&parse_expr("'hello'?.matches(`[a-z]+`)"))
            .unwrap();

        assert_eq!(
            compiled,
            Expr::ternary(
                Expr::neq(
                    Expr::const_expr(Value::String(Cow::Owned("hello".to_string()))),
                    Expr::const_expr(Value::Null),
                ),
                Expr::regex_match(
                    Expr::const_expr(Value::String(Cow::Owned("hello".into()))),
                    fancy_regex::Regex::new("[a-z]+").unwrap().into(),
                ),
                Expr::const_expr(Value::Null),
            ),
        )
    }

    #[test]
    fn compile_int_cmp() {
        let compiled = Compiler::for_spec(&parse_spec("node NodeKind {}"))
            .expr(&parse_expr("10 < 35"))
            .unwrap();

        assert_eq!(
            compiled,
            Expr::lt(Expr::Const(Value::Int(10)), Expr::Const(Value::Int(35)))
        )
    }

    #[test]
    fn compile_string_lit() {
        let compiled = Compiler::for_spec(&parse_spec("node NodeKind { }"))
            .expr(&parse_expr("\"hello\""))
            .unwrap();

        assert_eq!(
            compiled,
            Expr::const_expr(Value::String(Cow::Owned("hello".to_string())))
        )
    }

    #[test]
    fn compile_neq() {
        let compiled = Compiler::for_spec(&parse_spec("node NodeKind { }"))
            .expr(&parse_expr("1 != 0"))
            .unwrap();

        assert_eq!(
            compiled,
            Expr::neq(Expr::Const(1.into()), Expr::Const(0.into()))
        )
    }

    #[test]
    fn compile_null() {
        let compiled = Compiler::for_spec(&parse_spec("node NodeKind { }"))
            .expr(&parse_expr("null"))
            .unwrap();

        assert_eq!(compiled, Expr::const_expr(Value::Null))
    }

    #[test]
    fn trivial_with_predicate() {
        let spec = parse_spec("node NodeKind { }");

        let kind_id = spec.syntax.kind_id("NodeKind").unwrap();

        let compiled =
            compile(&spec, &parse_query("match NodeKind when 10 < 11").unwrap()).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::eq_eq(
                    Expr::kind_access(Expr::read_var(DEFAULT_INPUT_ADDR)),
                    Expr::const_expr(kind_id.into()),
                ),
                Expr::lt(
                    Expr::const_expr(Value::Int(10)),
                    Expr::const_expr(Value::Int(11)),
                ),
            )
        );
    }

    #[test]
    fn compile_parent_access() {
        let spec = parse_spec("node NodeKind { }");
        let query = parse_query("match _ n when n.parent == n").unwrap();
        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(true.into()),
                Expr::eq_eq(
                    Expr::node_parent(Expr::read_var(DEFAULT_INPUT_ADDR)),
                    Expr::read_var(DEFAULT_INPUT_ADDR),
                ),
            )
        );
    }

    #[test]
    fn compile_children_access() {
        let spec = parse_spec("node NodeKind { }");
        let query = parse_query("match _ n when n.children.length == 0").unwrap();
        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(true.into()),
                Expr::eq_eq(
                    Expr::length(Expr::node_children(Expr::read_var(DEFAULT_INPUT_ADDR))),
                    Expr::Const(0.into()),
                ),
            )
        )
    }

    #[test]
    fn compile_kind_access() {
        let spec = parse_spec(indoc!(
            "
            node NodeKind { }
        "
        ));

        let query = parse_query("match _ n when n.kind == n.kind").unwrap();

        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(true.into()),
                Expr::eq_eq(
                    Expr::kind_access(Expr::read_var(DEFAULT_INPUT_ADDR)),
                    Expr::kind_access(Expr::read_var(DEFAULT_INPUT_ADDR)),
                ),
            )
        )
    }

    #[test]
    fn field_values_pattern() {
        let spec = parse_spec(indoc!(
            "
            node NodeKind {
                field1: NodeKind,
                field2: OtherNodeKind
            }

            node OtherNodeKind { }
        "
        ));

        let query = parse_query("match NodeKind(field1: 'code', field2: OtherNodeKind)").unwrap();

        let compiled = compile(&spec, &query).unwrap();

        let node_kind = spec.syntax.kind_id("NodeKind").unwrap();
        let other_kind = spec.syntax.kind_id("OtherNodeKind").unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::and(
                    Expr::eq_eq(
                        Expr::kind_access(Expr::read_var(0)),
                        Expr::Const(Value::Kind(node_kind)),
                    ),
                    Expr::eq_eq(
                        Expr::prop_access(Expr::read_var(0), "field1".to_string()),
                        Expr::Const(Value::String(Cow::Owned("code".to_string()))),
                    ),
                ),
                Expr::in_context(
                    vec![Expr::prop_access(Expr::read_var(0), "field2".to_string())],
                    Expr::and(
                        Expr::neq(Expr::read_var(1), Expr::Const(Value::Null)),
                        Expr::eq_eq(
                            Expr::kind_access(Expr::read_var(1)),
                            Expr::Const(Value::Kind(other_kind))
                        ),
                    ),
                ),
            )
        )
    }

    #[test]
    fn compile_array_index() {
        let spec = parse_spec(indoc!("node NodeKind { }"));
        let query = parse_query("match _ n when n.children[0] != null").unwrap();
        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::Const(true.into()),
                Expr::neq(
                    Expr::array_index(
                        Expr::node_children(Expr::read_var(DEFAULT_INPUT_ADDR)),
                        Expr::Const(0.into()),
                    ),
                    Expr::Const(Value::Null),
                ),
            )
        )
    }

    #[test]
    fn compile_prev_sibling() {
        let spec = parse_spec("node NodeKind { }");
        let query = parse_query("match _ n when n.previous_sibling != null").unwrap();
        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(true.into()),
                Expr::neq(
                    Expr::node_prev_sibling(Expr::read_var(DEFAULT_INPUT_ADDR)),
                    Expr::const_expr(Value::Null),
                ),
            )
        );
    }

    #[test]
    fn compile_next_sibling() {
        let spec = parse_spec("node NodeKind { }");
        let query = parse_query("match _ n when n.next_sibling != null").unwrap();
        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(true.into()),
                Expr::neq(
                    Expr::node_next_sibling(Expr::read_var(0)),
                    Expr::const_expr(Value::Null),
                ),
            )
        );
    }

    #[test]
    fn compile_kind_check() {
        let spec_str = "node NodeKind { }";
        let spec = parse_spec(spec_str);
        let query = parse_query("match NodeKind").unwrap();

        let compiled = compile(&spec, &query).unwrap();

        let kind_id = spec.syntax.existing_kind_id("NodeKind");

        assert_eq!(
            compiled,
            Expr::eq_eq(
                Expr::kind_access(Expr::read_var(DEFAULT_INPUT_ADDR)),
                Expr::const_expr(kind_id.into()),
            )
        )
    }

    #[test]
    fn compile_kind_check_with_inheritance_parent() {
        let spec = parse_spec(indoc!(
            "
            node Parent { }
            node Child: Parent { }
        "
        ));

        let query = parse_query("match Parent").unwrap();

        let parent_kind = spec.syntax.kind_id("Parent").unwrap();
        let child_kind = spec.syntax.kind_id("Child").unwrap();

        assert_eq!(
            compile(&spec, &query).unwrap(),
            Expr::or(
                Expr::eq_eq(
                    Expr::kind_access(Expr::read_var(DEFAULT_INPUT_ADDR)),
                    Expr::const_expr(parent_kind.into()),
                ),
                Expr::eq_eq(
                    Expr::kind_access(Expr::read_var(DEFAULT_INPUT_ADDR)),
                    Expr::const_expr(child_kind.into()),
                ),
            )
        );
    }

    #[test]
    fn compile_quantifier_no() {
        let spec = parse_spec("node NodeKind {}");
        let query = parse_query("match _ n when no n.children match { NodeKind }").unwrap();
        let compiled = compile(&spec, &query).unwrap();

        let kind = spec.syntax.kind_id("NodeKind");

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(true.into()),
                Expr::in_context(
                    vec![Expr::node_children(Expr::read_var(DEFAULT_INPUT_ADDR))],
                    Expr::count_check_max(
                        Expr::const_expr(0.into()),
                        Expr::read_var(1),
                        Expr::eq_eq(
                            Expr::kind_access(Expr::read_var(2)),
                            Expr::const_expr(kind.into()),
                        ),
                    ),
                ),
            ),
        )
    }

    #[test]
    fn compile_quantifier_any() {
        let spec = parse_spec("node NodeKind {}");
        let query = parse_query("match _ n when any n.children match { NodeKind }").unwrap();
        let compiled = compile(&spec, &query).unwrap();

        let kind = spec.syntax.kind_id("NodeKind");

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(true.into()),
                Expr::in_context(
                    vec![Expr::node_children(Expr::read_var(DEFAULT_INPUT_ADDR))],
                    Expr::count_check_min(
                        Expr::const_expr(1.into()),
                        Expr::read_var(1),
                        Expr::eq_eq(
                            Expr::kind_access(Expr::read_var(2)),
                            Expr::const_expr(kind.into()),
                        ),
                    ),
                ),
            ),
        )
    }

    #[test]
    fn compile_quantifier_all() {
        let spec = parse_spec("node NodeKind {}");
        let query = parse_query("match _ n when all n.children match { NodeKind }").unwrap();
        let compiled = compile(&spec, &query).unwrap();

        let kind = spec.syntax.kind_id("NodeKind");

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(true.into()),
                Expr::in_context(
                    vec![Expr::node_children(Expr::read_var(DEFAULT_INPUT_ADDR))],
                    Expr::count_check_min(
                        Expr::length(Expr::read_var(1)),
                        Expr::read_var(1),
                        Expr::eq_eq(
                            Expr::kind_access(Expr::read_var(2)),
                            Expr::const_expr(kind.into()),
                        ),
                    ),
                ),
            ),
        )
    }

    #[test]
    fn compile_kind_check_with_inheritance_child() {
        let spec = parse_spec(indoc!(
            "
            node Parent { }
            node Child: Parent { }
        "
        ));

        let query = parse_query("match Child").unwrap();
        let child_kind = spec.syntax.kind_id("Child").unwrap();

        assert_eq!(
            compile(&spec, &query).unwrap(),
            Expr::eq_eq(
                Expr::kind_access(Expr::read_var(DEFAULT_INPUT_ADDR)),
                Expr::const_expr(child_kind.into()),
            )
        );
    }

    #[test]
    fn compile_placeholder() {
        let spec_str = "node NodeKind { }";
        let spec = parse_spec(spec_str);
        let query = parse_query("match _").unwrap();

        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(compiled, Expr::Const(Value::Bool(true)))
    }

    #[test]
    fn compile_dot_access() {
        let spec_str = "node NodeKind { }";
        let spec = parse_spec(spec_str);
        let query = parse_query("match _ n when n.text.length == 10").unwrap();

        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(Value::Bool(true)),
                Expr::eq_eq(
                    Expr::length(Expr::node_text(Expr::read_var(0))),
                    Expr::const_expr(Value::Int(10)),
                ),
            )
        );
    }

    #[test]
    fn compile_field_access() {
        let spec = parse_spec(indoc!(
            "
            node A {
                field: B
            }
            
            node B { } 
        "
        ));

        let query = parse_query("match A a when a.field != null").unwrap();
        let a_kind = spec.syntax.kind_id("A");
        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::eq_eq(
                    Expr::kind_access(Expr::read_var(DEFAULT_INPUT_ADDR)),
                    Expr::const_expr(a_kind.into()),
                ),
                Expr::neq(
                    Expr::prop_access(Expr::read_var(DEFAULT_INPUT_ADDR), "field".into()),
                    Expr::Const(Value::Null),
                ),
            )
        )
    }

    #[test]
    fn compile_safe_field_access() {
        let spec = parse_spec(indoc!(
            "
            node A {
                field: B
            }
            
            node B { } 
        "
        ));

        let query = parse_query("match A a when a?.field != null").unwrap();
        let a_kind = spec.syntax.kind_id("A");
        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::eq_eq(
                    Expr::kind_access(Expr::read_var(DEFAULT_INPUT_ADDR)),
                    Expr::const_expr(a_kind.into()),
                ),
                Expr::neq(
                    Expr::ternary(
                        Expr::neq(
                            Expr::read_var(DEFAULT_INPUT_ADDR),
                            Expr::const_expr(Value::Null),
                        ),
                        Expr::prop_access(Expr::read_var(DEFAULT_INPUT_ADDR), "field".into()),
                        Expr::const_expr(Value::Null),
                    ),
                    Expr::Const(Value::Null),
                ),
            )
        )
    }

    #[test]
    fn compile_invalid_field_access() {
        let spec = parse_spec("node A {}");
        let query = parse_query("match A a when a.field != null").unwrap();
        let compiled = compile(&spec, &query);

        assert_eq!(
            compiled,
            Err(CompilationErr::InvalidPropertyName("field".to_string()))
        );
    }

    #[test]
    fn compile_hte() {
        let spec = parse_spec("node A { }");
        let query = parse_query("match _ when 10 >= 9").unwrap();

        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(Value::Bool(true)),
                Expr::hte(
                    Expr::const_expr(Value::Int(10)),
                    Expr::const_expr(Value::Int(9)),
                ),
            )
        )
    }

    #[test]
    fn compile_and() {
        let spec = parse_spec("node A { }");
        let query = parse_query("match _ when 0 < 1 && 3 > 2").unwrap();

        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(Value::Bool(true)),
                Expr::and(
                    Expr::lt(
                        Expr::const_expr(Value::Int(0)),
                        Expr::const_expr(Value::Int(1)),
                    ),
                    Expr::ht(
                        Expr::const_expr(Value::Int(3)),
                        Expr::const_expr(Value::Int(2)),
                    ),
                ),
            )
        );
    }

    #[test]
    fn compile_is() {
        let spec = parse_spec("node NodeKind { }");
        let query = parse_query("match _ n when n is { NodeKind }").unwrap();
        let compiled = compile(&spec, &query).unwrap();

        let kind_id = spec.syntax.kind_id("NodeKind").unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(true.into()),
                Expr::in_context(
                    vec![Expr::read_var(DEFAULT_INPUT_ADDR)],
                    Expr::and(
                        Expr::non_null_check(Expr::read_var(1)),
                        Expr::eq_eq(
                            Expr::kind_access(Expr::read_var(1)),
                            Expr::const_expr(kind_id.into()),
                        ),
                    ),
                ),
            )
        )
    }

    #[test]
    fn compile_nested_is() {
        let spec = parse_spec("node NodeKind {}");
        let query =
            parse_query("match _ n when n.parent is { _ p when p.parent is { _ pp } }").unwrap();
        let compiled = compile(&spec, &query).unwrap();

        assert_eq!(
            compiled,
            Expr::and(
                Expr::const_expr(true.into()),
                Expr::in_context(
                    vec![Expr::node_parent(Expr::read_var(DEFAULT_INPUT_ADDR))],
                    Expr::and(
                        Expr::non_null_check(Expr::read_var(1)),
                        Expr::and(
                            Expr::const_expr(true.into()),
                            Expr::in_context(
                                vec![Expr::node_parent(Expr::read_var(1))],
                                Expr::and(
                                    Expr::non_null_check(Expr::read_var(2)),
                                    Expr::const_expr(true.into()),
                                ),
                            ),
                        ),
                    ),
                ),
            )
        );
    }
}
