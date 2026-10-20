use super::{Error,FIBRE_COUNT};
macro_rules! index_type {
    ($name:ident, $bound:expr) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct $name(usize);
        impl $name {
            pub fn new(index: usize) -> Result<Self, Error> {
                if index < $bound {
                    Ok(Self(index))
                } else {
                    Err(Error::IndexOutOfRange)
                }
            }
            pub const fn get(self) -> usize {
                self.0
            }
        }
    };
}
index_type!(FibreIndex, FIBRE_COUNT);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Point<E> {
    pub x: E,
    pub y: E,
}

