use pest::{
    iterators::{Pair, Pairs},
    RuleType,
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum WalkError<R: RuleType> {
    #[error("missing child while walking the parse tree")]
    MissingChild,
    #[error("unexpected token: got {0} but expected {1:?}")]
    UnexpectedToken(String, Vec<String>),
    #[error("unexpected rule: got {0:?} but expected {1:?}")]
    UnexpectedRule(R, Vec<R>),
}

pub trait Walkable<O, R: RuleType>
where
    Self: Sized,
{
    fn next_child(&mut self) -> Result<O, WalkError<R>>;
}

impl<'a, R: RuleType> Walkable<Pair<'a, R>, R> for Pairs<'a, R> {
    fn next_child(&mut self) -> Result<Pair<'a, R>, WalkError<R>> {
        match self.next() {
            Some(child) => Ok(child),
            None => Err(WalkError::MissingChild),
        }
    }
}

pub fn unexpected_rule<R: RuleType, T>(actual: R, expected: Vec<R>) -> Result<T, WalkError<R>> {
    Err(WalkError::UnexpectedRule(actual, expected))
}
