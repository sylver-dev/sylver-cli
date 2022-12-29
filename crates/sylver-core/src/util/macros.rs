#[macro_export]
macro_rules! id_type {
    ($x:ident : $inner:ty) => {
        #[derive(Debug, Copy, Clone, derive_more::From, derive_more::Into, Eq, PartialEq, Hash)]
        pub struct $x(Id<$inner>);

        impl $x {
            pub fn index(self) -> usize {
                self.0.index_value()
            }
        }

        impl PartialOrd for $x {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.index().partial_cmp(&other.index())
            }
        }

        impl Ord for $x {
            fn cmp(&self, other: &Self) -> Ordering {
                self.index().cmp(&other.index())
            }
        }

        impl From<usize> for $x {
            fn from(x: usize) -> $x {
                $x(Id::from_index(x))
            }
        }

        impl std::fmt::Display for $x {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.index())
            }
        }
    };
}
