#[cfg(not(feature = "private-leaf-salts"))]
pub const SECOND_QUERY_BYTES:usize=4*32+6*7*32;