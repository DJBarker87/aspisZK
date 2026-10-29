//! Owned expressions of the differing reached Rust 1.94.1 conversion bodies.
//! Source mapping: std227-comparison-construct-resume5.json.
pub fn from_u32_u64(small:u32)->u64 { small as u64 }
pub fn from_bool_u32(small:bool)->u32 { small as u8 as u32 }
pub fn from_u16_usize(small:u16)->usize { small as usize }
pub fn from_u8_usize(small:u8)->usize { small as usize }
