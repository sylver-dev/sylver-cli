use fancy_regex::{Match, Regex};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use sylver_dsl::meta::*;

use crate::{
    core::{
        pos::{InclPosRange, Pos},
        spec::TagId,
    },
    parsing::lexer_regex::LexerRegex,
};

#[derive(Debug, Eq, PartialEq, Copy, Clone, Hash)]
pub struct TokenRes {
    pub token: Token,
    pub updated_pos: Pos,
}

#[derive(Debug, Eq, PartialEq, Copy, Clone, Hash)]
pub struct Token {
    pub pos: InclPosRange,
    pub tag: TagId,
}

impl Token {
    pub fn new(pos: InclPosRange, tag: TagId) -> Token {
        Token { pos, tag }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RegularTokenType {
    Regex,
    Literal,
}

#[derive(Debug, Clone)]
pub enum TokenDesc {
    Regular(RegularTokenType, LexerRegex),
    Nested(LexerRegex, Regex),
}

#[derive(Debug, Clone)]
pub struct Scanner {
    tokens: FxHashMap<TagId, TokenDesc>,
}

impl Scanner {
    pub fn new(defs: impl IntoIterator<Item = (TagId, TermContent)>) -> anyhow::Result<Scanner> {
        let tokens = defs
            .into_iter()
            .map(|(tag, content)| {
                let token_desc = match content {
                    TermContent::Literal(r) => {
                        TokenDesc::Regular(RegularTokenType::Literal, r.try_into()?)
                    }
                    TermContent::Regex(r) => {
                        TokenDesc::Regular(RegularTokenType::Regex, r.try_into()?)
                    }
                    TermContent::Nested(start, stop) => TokenDesc::Nested(
                        start.try_into()?,
                        <LexerRegex>::try_from(stop)?.multiline(),
                    ),
                };

                Ok((tag, token_desc))
            })
            .collect::<anyhow::Result<FxHashMap<TagId, TokenDesc>>>()?;

        Ok(Scanner { tokens })
    }

    pub fn tokens_for_tags(
        &self,
        input: &str,
        pos: Pos,
        tags: impl IntoIterator<Item = TagId>,
    ) -> SmallVec<[TokenRes; 6]> {
        let mut tokens: SmallVec<[TokenRes; 6]> = tags
            .into_iter()
            .filter_map(|tag| self.build_token(input, pos, tag))
            .collect();

        tokens.sort_by_key(|t: &TokenRes| {
            let sort_id =
                i32::from(self.token_type_for_tag(t.token.tag) != Some(RegularTokenType::Literal));

            (-(t.updated_pos.txt_pos as i64), sort_id)
        });

        let first = if let Some(r) = tokens.first() {
            *r
        } else {
            return SmallVec::new();
        };

        let mut current_pos = first.updated_pos.txt_pos;
        let mut current_is_literal =
            self.token_type_for_tag(first.token.tag) == Some(RegularTokenType::Literal);

        let mut res = SmallVec::new();

        res.push(first);

        for &r in &tokens[1..] {
            let token_type = self.token_type_for_tag(r.token.tag);

            let should_keep = r.updated_pos.txt_pos() >= current_pos
                && !(current_is_literal && token_type == Some(RegularTokenType::Regex));

            if should_keep {
                res.push(r);
                current_pos = r.updated_pos.txt_pos;
                current_is_literal = token_type == Some(RegularTokenType::Literal);
            }
        }

        res
    }

    fn token_type_for_tag(&self, tag: TagId) -> Option<RegularTokenType> {
        let token = self.tokens.get(&tag).unwrap();

        if let TokenDesc::Regular(t, _) = token {
            Some(*t)
        } else {
            None
        }
    }

    pub fn build_token(&self, input: &str, pos: Pos, tag: TagId) -> Option<TokenRes> {
        let match_str = self.get_match_str(input, pos, tag)?;
        let (end, updated_pos) = compute_end_and_current_pos(match_str, pos);
        let token = Token::new(
            InclPosRange::new(pos, end).expect("start pos should be before end_pos"),
            tag,
        );
        Some(TokenRes { token, updated_pos })
    }

    fn get_match_str<'i>(&self, input: &'i str, pos: Pos, tag: TagId) -> Option<&'i str> {
        let desc = self.tokens.get(&tag).expect("Invalid tag !");
        let input_at_pos = &input[pos.txt_pos..];

        match desc {
            TokenDesc::Nested(start, stop) => Scanner::match_nested(input_at_pos, start, stop),
            TokenDesc::Regular(_, r) => Scanner::match_regular(input_at_pos, r),
        }
    }

    fn match_regular<'i>(input: &'i str, regex: &LexerRegex) -> Option<&'i str> {
        if let Some(m) = regex.find(input) {
            Some(m.as_str())
        } else {
            None
        }
    }

    fn match_nested<'i>(
        input: &'i str,
        start_regex: &LexerRegex,
        end_regex: &Regex,
    ) -> Option<&'i str> {
        let mut nesting = 0;
        let mut offset = 0;
        let mut start_match = start_regex.find(input);
        let mut end_match = find_reg(end_regex, input);

        while start_match.is_some() || end_match.is_some() {
            if let Some(s) = start_match {
                if s.start() < end_match.map(|e| e.start()).unwrap_or(usize::MAX) {
                    nesting += 1;
                    offset += s.end();
                }
            }

            if let Some(e) = end_match {
                if e.start() < start_match.map(|s| s.start()).unwrap_or(usize::MAX) {
                    offset += e.end();
                    nesting -= 1;

                    if nesting == 0 {
                        return Some(&input[0..offset]);
                    }
                }
            }

            start_match = start_regex.find(&input[offset..]);
            end_match = find_reg(end_regex, &input[offset..]);
        }

        None
    }
}

fn find_reg<'i>(reg: &Regex, input: &'i str) -> Option<Match<'i>> {
    reg.find(input).unwrap_or(None)
}

fn compute_end_and_current_pos(m: &str, start_pos: Pos) -> (Pos, Pos) {
    let mut end = start_pos;
    let mut current = start_pos;

    end = end.add_to_text_pos(m.len() - 1); // end position is inclusive
    current = current.add_to_text_pos(m.len());

    for c in m.chars() {
        // end is equal to currentPos - 1 iteration as its token position is inclusive
        end = current;

        if c == '\n' {
            current = current.set_col(1);
            current = current.add_to_line(1);
        } else {
            current = current.add_to_col(1);
        }
    }

    (end, current)
}

#[cfg(test)]
pub mod test {
    use id_vec::Id;

    use sylver_dsl::test::parse_term_content;

    use super::*;

    #[test]
    fn lex_hello() {
        let id_hello = Id::from_index(0).into();

        test_lexer_ok(
            vec![(id_hello, parse_term_content("'hello'"))],
            "hellohello",
            vec![("hello", id_hello), ("hello", id_hello)],
        )
    }

    #[test]
    fn lex_ambiguous() {
        let id_hello = Id::from_index(0).into();
        let id_identifier = Id::from_index(1).into();

        test_lexer_ok(
            vec![
                (id_hello, parse_term_content("'hello'")),
                (id_identifier, parse_term_content("`hello|world`")),
            ],
            "hellohellohello",
            vec![
                ("hello", id_hello),
                ("hello", id_identifier),
                ("hello", id_hello),
            ],
        )
    }

    #[test]
    fn nested_comments_sequence() {
        let hello_id = 1.into();
        let comment_id = 2.into();

        test_lexer_ok(
            vec![
                (hello_id, parse_term_content("'hello'")),
                (
                    comment_id,
                    TermContent::Nested(
                        Regex::new(&fancy_regex::escape("/*")).unwrap(),
                        Regex::new(&fancy_regex::escape("*/")).unwrap(),
                    ),
                ),
            ],
            "hello/*hello*/hello/**/",
            vec![
                ("hello", hello_id),
                ("/*hello*/", comment_id),
                ("hello", hello_id),
                ("/**/", comment_id),
            ],
        )
    }

    #[test]
    fn multiline_nested_comment() {
        let hello_id = 1.into();
        let comment_id = 2.into();

        test_lexer_ok(
            vec![
                (hello_id, parse_term_content("'hello'")),
                (
                    comment_id,
                    TermContent::Nested(
                        Regex::new(&fancy_regex::escape("/*")).unwrap(),
                        Regex::new(&fancy_regex::escape("*/")).unwrap(),
                    ),
                ),
            ],
            "hello/*hello\n\n*/hello/**/",
            vec![
                ("hello", hello_id),
                ("/*hello\n\n*/", comment_id),
                ("hello", hello_id),
                ("/**/", comment_id),
            ],
        )
    }

    #[test]
    fn literal_over_regex() {
        let true_id = 1.into();
        let id_id = 2.into();

        let scanner = Scanner::new(vec![
            (true_id, parse_term_content("'true'")),
            (id_id, parse_term_content("`[a-z]+`")),
        ])
        .unwrap();

        let input = "true";

        let res = scanner.tokens_for_tags(input, Pos::new((0, 0), 0), vec![true_id, id_id]);

        assert_eq!(1, res.len());
        assert_eq!(true_id, res[0].token.tag);
    }

    fn test_lexer_ok(rules: Vec<(TagId, TermContent)>, input: &str, expected: Vec<(&str, TagId)>) {
        let scanner = Scanner::new(rules.into_iter()).unwrap();

        let mut pos = Pos::default();
        let mut result = vec![];

        for (_, tag_id) in &expected {
            let t = scanner.tokens_for_tags(input, pos, vec![*tag_id]);
            assert_eq!(1, t.len());
            assert_eq!(*tag_id, t[0].token.tag);
            pos = t[0].updated_pos;
            result.push((
                &input[t[0].token.pos.start().txt_pos()..t[0].token.pos.end().txt_pos()],
                t[0].token.tag,
            ));
        }

        assert_eq!(expected, result);
    }
}
