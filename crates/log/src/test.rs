use super::*;

#[derive(Debug, Clone, Default)]
pub struct TestLogger {}

impl Logger for TestLogger {
    fn scoped(&self, _msg: &str, _done_msg: Option<&str>) -> Box<dyn ScopedMsg> {
        Box::new(())
    }

    fn info(&self, _msg: &str) {}

    fn error(&self, _msg: &str) {}
}

impl ScopedMsg for () {}
