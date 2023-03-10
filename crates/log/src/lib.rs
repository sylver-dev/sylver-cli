pub mod fancy;
use std::fmt::Debug;

pub use fancy::*;
pub use test::*;

pub mod test;

pub trait Logger: Debug + Send + Sync {
    fn scoped(&self, msg: &str, done_msg: Option<&str>) -> Box<dyn ScopedMsg>;

    fn error(&self, msg: &str);

    fn success(&self, msg: &str);

    fn important(&self, msg: &str);

    fn info(&self, msg: &str);
}

pub trait ScopedMsg {}
