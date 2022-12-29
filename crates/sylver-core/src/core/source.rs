use std::{
    fs::read_to_string,
    ops::Index,
    path::{Path, PathBuf},
};

use anyhow::Context;

use crate::{
    core::{pos::Pos, spec::TagId},
    parsing::{scanner::Token, sppf::TokenPos},
    tree::{Node, NodeId, Tree},
};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum SourceOrigin {
    File(PathBuf),
    Inline(String),
}

impl SourceOrigin {
    pub fn path(&self) -> &Path {
        match self {
            SourceOrigin::File(path) => path,
            SourceOrigin::Inline(id) => id.as_ref(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Source {
    src: String,
    origin: SourceOrigin,
}

impl Source {
    /// Create a new `Source` from a file.
    pub fn file(src: String, path: PathBuf) -> Source {
        Source {
            src,
            origin: SourceOrigin::File(path),
        }
    }

    /// Create a new `Source` from inline code.
    pub fn inline(src: String, id: String) -> Source {
        Source {
            src,
            origin: SourceOrigin::Inline(id),
        }
    }

    pub fn path(&self) -> &Path {
        self.origin.path()
    }

    pub fn src(&self) -> &String {
        &self.src
    }

    pub fn code_between(&self, start: Pos, end: Pos) -> &str {
        &self.src[start.txt_pos()..end.txt_pos()]
    }
}

pub fn source_from_file(f: &Path) -> anyhow::Result<Source> {
    let source_str =
        read_to_string(f).with_context(|| format!("Can not read source file: {}", f.display()))?;

    Ok(Source::file(source_str, f.to_path_buf()))
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct SourceTree {
    pub source: Source,
    pub tokens: Vec<Token>,
    pub tree: Tree,
}

impl SourceTree {
    /// Create a new `SourceTree`.
    pub fn new(source: Source, tokens: Vec<Token>, tree: Tree) -> SourceTree {
        SourceTree {
            source,
            tokens,
            tree,
        }
    }

    pub fn existing_token(&self, pos: TokenPos) -> &Token {
        &self.tokens[pos]
    }

    /// Return the source code for the token at the given position.
    /// # panics
    /// If there is no token at the given position.
    pub fn token_code(&self, token_pos: usize) -> &str {
        let token = self.tokens[token_pos];
        self.code_between(token, token)
    }

    /// Return the node's text: it's code after stripping leading/trailing ignore tokens.
    /// # panics
    /// If there is no node with the given id.
    pub fn node_text(&self, node_id: NodeId, ignore: &[TagId]) -> &str {
        self.tokens_code(self.node_tokens(node_id, ignore))
    }

    /// Return the source code for the given tree node, including ignore tokens.
    /// # panics
    /// If there is no node with the given id.
    pub fn node_code(&self, node_id: NodeId) -> &str {
        self.tokens_code(self.node_tokens_with_ignore(node_id))
    }

    /// Return a slice of tokens for the given node, without ignored tokens.
    /// # panics
    /// If there is no node with the given id.
    pub fn node_tokens(&self, node_id: NodeId, ignore: &[TagId]) -> &[Token] {
        let is_not_ignore = |t: &Token| !ignore.contains(&t.tag);

        let tokens = self.node_tokens_with_ignore(node_id);

        let bounds = tokens
            .iter()
            .position(is_not_ignore)
            .zip(tokens.iter().rposition(is_not_ignore));

        bounds
            .map(|(first, last)| &tokens[first..=last])
            .unwrap_or(tokens)
    }

    /// Return a slice of tokens for the given node, including ignored tokens.
    /// # panics
    /// If there is no node with the given id.
    pub fn node_tokens_with_ignore(&self, node_id: NodeId) -> &[Token] {
        let node = &self.tree[node_id];

        match node.span.end() {
            Some(end) => &self.tokens[node.span.start..=end],
            _ => &[],
        }
    }
    pub fn tokens_code(&self, tokens: &[Token]) -> &str {
        tokens
            .first()
            .zip(tokens.last())
            .map(|(first, last)| self.code_between(*first, *last))
            .unwrap_or("")
    }

    pub fn code_between(&self, first: Token, last: Token) -> &str {
        self.source.code_between(first.pos.start(), last.pos.end())
    }
}

impl Index<NodeId> for SourceTree {
    type Output = Node;

    fn index(&self, index: NodeId) -> &Self::Output {
        &self.tree[index]
    }
}

impl Index<TokenPos> for SourceTree {
    type Output = Token;

    fn index(&self, index: TokenPos) -> &Self::Output {
        &self.tokens[index]
    }
}

#[cfg(test)]
pub mod test {
    use crate::{
        core::{pos::InclPosRange, spec::test::test_syntax},
        tree::TreeBuilder,
    };

    use super::*;

    pub fn create_test_source_tree(code: &str) -> SourceTree {
        let lines = code.lines().count();
        let last_line_len = code.lines().last().map(|l| l.len()).unwrap_or_default();

        let source = Source::inline(code.to_string(), format!("{code}_id"));

        let syntax = test_syntax();
        let mut editor = TreeBuilder::new(&syntax);

        editor.add_token(Token::new(
            InclPosRange::new(
                Pos::new((1, 1), 0),
                Pos::new((lines, last_line_len), code.len() - 1),
            )
            .unwrap(),
            0.into(),
        ));

        editor.add_node(1.into(), &vec![], &[0]);

        let (tree, tokens) = editor.build();

        SourceTree::new(source, tokens, tree)
    }
}
