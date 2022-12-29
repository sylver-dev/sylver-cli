use anyhow::{anyhow, Context, Result};
use derive_more::Display;
use fancy_regex::{Match, Regex};

#[derive(Debug, Clone, Display)]
pub struct LexerRegex {
    regex: Regex,
}

impl LexerRegex {
    /// Tries to parse the given string to build a new `LexerRegex`.
    pub fn new(regex: &str) -> Result<LexerRegex> {
        // The pattern is wrapped in \A(...) so that it starts matching from the beginning of the
        // input.
        let updated_reg = Regex::new(&format!("\\A({regex})"))
            .with_context(|| format!("Could not parse regex: {regex}"))?;

        if matches!(updated_reg.is_match(""), Ok(true)) {
            return Err(anyhow!(
                "Regex {regex} cannot be used in the lexer: empty string matches."
            ));
        }

        Ok(LexerRegex { regex: updated_reg })
    }

    /// Return a multi-line `LexerRegex` matching the same pattern as self.
    pub fn multiline(&self) -> Regex {
        Regex::new(&format!("(?m){}", self.as_str())).unwrap()
    }

    /// Return the regex as a string, without stripping away the wrapping \A(...)
    pub fn as_raw_str(&self) -> &str {
        self.regex.as_str()
    }

    /// Return the regex as a string, stripping away the wrapping \A(...)
    pub fn as_str(&self) -> &str {
        &self.regex.as_str()[3..self.regex.as_str().len() - 1]
    }

    pub fn find<'t>(&self, txt: &'t str) -> Option<Match<'t>> {
        match self.regex.find(txt) {
            Err(_) => None,
            Ok(m) => m,
        }
    }

    pub fn regex(&self) -> &Regex {
        &self.regex
    }
}

impl TryFrom<Regex> for LexerRegex {
    type Error = anyhow::Error;

    fn try_from(value: Regex) -> std::result::Result<Self, Self::Error> {
        LexerRegex::new(value.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_ok() {
        let reg = LexerRegex::new("hello").unwrap();
        assert_eq!(
            Regex::new("\\A(hello)").unwrap().as_str(),
            reg.regex.as_str()
        );
    }

    #[test]
    fn build_error_invalid_regex() {
        let reg = LexerRegex::new("*");
        assert!(reg.is_err());
    }

    #[test]
    fn build_error_matches_empty_string() {
        let reg = LexerRegex::new("a?").err().unwrap();
        assert_eq!(
            reg.to_string(),
            "Regex a? cannot be used in the lexer: empty string matches.".to_string()
        )
    }

    #[test]
    fn as_str_strips_wrapping_pattern() {
        let reg = LexerRegex::new("hello").unwrap();
        assert_eq!("hello", reg.as_str());
    }

    #[test]
    fn find_ok() {
        let reg = LexerRegex::new("hello").unwrap();
        assert_eq!("hello", reg.find("hello").unwrap().as_str())
    }

    #[test]
    fn find_not_ok() {
        let reg = LexerRegex::new("hello").unwrap();
        assert_eq!(None, reg.find("42"));
    }

    #[test]
    fn multi_line() {
        let reg = LexerRegex::new("hello").unwrap();
        assert_eq!("(?m)hello", reg.multiline().as_str());
    }
}
