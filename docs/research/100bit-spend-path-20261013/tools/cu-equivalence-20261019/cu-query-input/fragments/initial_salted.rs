#[cfg(feature = "private-leaf-salts")]
pub const INITIAL_QUERY_BYTES:usize=480+128+64+2*6*7*32;