use std::iter::repeat;

use itertools::Itertools;

use crate::{
    core::{
        pos::{InclPosRange, Pos},
        source::SourceTree,
        spec::Spec,
    },
    parsing::scanner::Token,
    tree::{
        info::{comment_childs, non_comment_childs, raw::RawTreeInfo, NodeProxy, TreeInfo},
        NodeId,
    },
};

pub fn render_node(spec: &Spec, source: &SourceTree, node: NodeId) -> String {
    let infos = RawTreeInfo::new(source, &spec.syntax);
    let node_proxy = infos.proxy(node);
    let kind_name = node_proxy.kind_name();
    let path = source.source.path();
    let position = infos.node_pos(node);
    format!(
        "[{} {}:{}]",
        kind_name,
        path.display(),
        render_pos_range(position)
    )
}

fn render_pos_range(range: InclPosRange) -> String {
    format!("{}-{}", render_pos(range.start()), render_pos(range.end()))
}

fn render_pos(pos: Pos) -> String {
    format!("{}:{}", pos.line, pos.col)
}

#[derive(Debug, Clone)]
pub struct PPrintConf {
    indentation: String,
}

impl Default for PPrintConf {
    fn default() -> Self {
        PPrintConf {
            indentation: ". ".into(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TreePPrint<'t, T: TreeInfo<'t>> {
    conf: PPrintConf,
    tree: T,
    ph: std::marker::PhantomData<&'t ()>,
}

impl<'t, T: TreeInfo<'t> + Clone> TreePPrint<'t, T> {
    pub fn new(tree: T) -> Self {
        TreePPrint {
            conf: Default::default(),
            tree,
            ph: Default::default(),
        }
    }

    pub fn render(&self) -> String {
        self.render_from(0, None, &self.tree.root())
    }

    pub fn render_from(
        &self,
        indentation: usize,
        name: Option<&str>,
        node: &NodeProxy<T>,
    ) -> String {
        let indentation_fmt = self.indentation_str(indentation);
        let name_repr = name.map(|n| format!("● {n}: ")).unwrap_or_default();
        let node_repr = self.render_node(node);
        let node_content = self.render_node_content(indentation, node);
        let (pre_content, post_content) = if node.direct_children().is_empty() {
            (" { ".to_string(), " }".to_string())
        } else {
            (" {\n".to_string(), format!("\n{indentation_fmt}}}"))
        };

        format!("{indentation_fmt}{name_repr}{node_repr}{pre_content}{node_content}{post_content}",)
    }

    pub fn render_node(&self, node: &NodeProxy<T>) -> String {
        node.kind_name().to_string()
    }

    fn render_node_content(&self, indentation: usize, node: &NodeProxy<T>) -> String {
        let comments = comment_childs(&self.tree, node);

        match non_comment_childs(&self.tree, node).len() {
            0 if comments.is_empty() => node.code().trim().to_string(),
            0 => self.render_tokens_and_comments(indentation + 1, node.tokens(), &comments),
            _ => node
                .children_with_name()
                .iter()
                .map(|(name, c)| self.render_from(indentation + 1, *name, c))
                .join("\n"),
        }
    }

    fn render_tokens_and_comments(
        &self,
        indentation: usize,
        tokens: &[Token],
        comment_nodes: &[NodeProxy<T>],
    ) -> String {
        let mut reprs = vec![];

        let non_ignore_tokens = tokens
            .iter()
            .filter(|t| !self.tree.ignore_tags().contains(&t.tag));

        for &t in non_ignore_tokens {
            let matching_comment = comment_nodes.iter().find(|n| n.contains_token(t));
            if let Some(comment) = matching_comment {
                if comment.tokens().first() == Some(&t) {
                    reprs.push(self.render_from(indentation + 1, None, comment));
                }
            } else {
                reprs.push(self.render_token(indentation + 1, t));
            };
        }

        reprs.join("\n")
    }

    fn render_token(&self, indentation: usize, token: Token) -> String {
        format!(
            "{}{}",
            self.indentation_str(indentation),
            self.tree.token_code(token)
        )
    }

    fn indentation_str(&self, level: usize) -> String {
        repeat(&self.conf.indentation).take(level).join("")
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use crate::{
        core::{source::Source, spec::Spec},
        parsing::parser_runner::ParserRunner,
        pretty_print::render_report,
        tree::info::raw::RawTreeInfo,
    };

    use super::*;

    #[test]
    fn trivial_with_name() {
        let spec = indoc!(
            "
            node A { }
            node B { field: A }

            rule a_node = A { 'a' }
            rule main = B { field@a_node }
        "
        );

        let code = indoc!("a");

        let expected = indoc!(
            r#"
            B {
            . ● field: A { a }
            }
        "#
        );

        test_pprint_ok(spec, code, expected.trim());
    }

    #[test]
    fn trivial_with_names() {
        let spec = indoc!(
            "
            node A { }
            node B { first: A, second: A }

            rule a_node = A { 'a' }
            rule main = B { first@a_node second@a_node }
        "
        );

        let code = indoc!("aa");

        let expected = indoc!(
            r#"
            B {
            . ● first: A { a }
            . ● second: A { a }
            }
        "#
        );

        test_pprint_ok(spec, code, expected.trim());
    }

    #[test]
    fn trivial_with_list() {
        let spec = indoc!(
            "
            node A { }
            node B { fields: List<A> }

            rule a_node = A { 'a' }
            rule main = B { fields@a_node* } 
            "
        );

        let code = indoc!("aa");

        let expected = indoc!(
            r#"
            B {
            . ● fields: List {
            . . A { a }
            . . A { a }
            . }
            }
        "#
        );

        test_pprint_ok(spec, code, expected.trim());
    }

    #[test]
    fn const_decl() {
        let spec = indoc!(
            "
            node Num { }
            node Identifier { }
            node ConstDecl { name: Identifier, num: Num }
            node Program { decls: List<ConstDecl> }

            ignore term WHITESPACE = `\\s`

            rule main = Program { decls@const_decl* }
            rule const_decl = ConstDecl { `const` name@ident `=` num@num_rule  }
            rule num_rule = Num { `[0-9]+` }
            rule ident = Identifier { `[a-zA-Z]+` }
        "
        );

        let code = indoc!(
            "
            const hello = 40
            const world = 2
        "
        );

        let expected = indoc!(
            r#"
            Program {
            . ● decls: List {
            . . ConstDecl {
            . . . ● name: Identifier { hello }
            . . . ● num: Num { 40 }
            . . }
            . . ConstDecl {
            . . . ● name: Identifier { world }
            . . . ● num: Num { 2 }
            . . }
            . }
            }
        "#
        );

        test_pprint_ok(spec, code, expected.trim());
    }

    #[test]
    fn optional_field_missing() {
        let spec = indoc!(
            "
            node A {
                field1: B,
                field2: C
            }

            node B { }

            node C { }

            rule b_node = B { 'b' }
            rule c_node = C { 'c' }
            rule main = A { field1@b_node? field2@c_node } 
        "
        );

        let code = indoc!("c");

        let expected = indoc!(
            r#"
            A {
            . ● field2: C { c }
            }
        "#
        );

        test_pprint_ok(spec, code, expected.trim());
    }

    fn test_pprint_ok(spec_str: &str, code: &str, expected: &str) {
        let spec_ast = sylver_dsl::meta::parse(spec_str).expect("Invalid spec str");
        let spec: Spec = Spec::from_decls(Default::default(), spec_ast).expect("Invalid spec");
        let parser_runner = ParserRunner::new("main", &spec.syntax).unwrap();

        let source = Source::inline(code.to_string(), "".to_string());

        let parsing_result = parser_runner.run([source]).pop().unwrap();

        for report in parsing_result.reports {
            eprintln!(
                "{}\n",
                render_report(true, &report, &parsing_result.tree.source).unwrap()
            )
        }

        let repr = TreePPrint::new(RawTreeInfo::new(&parsing_result.tree, &spec.syntax)).render();

        println!("{}", repr);

        assert_eq!(repr, expected);
    }
}
