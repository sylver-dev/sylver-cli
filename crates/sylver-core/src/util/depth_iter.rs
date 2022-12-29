#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct DepthVal<T> {
    pub val: T,
    pub depth: usize,
}
