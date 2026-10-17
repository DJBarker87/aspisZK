/// hashv-shaped backend: hash the concatenation of the input slices.
pub type HashFn = fn(&[&[u8]]) -> [u8; 32];