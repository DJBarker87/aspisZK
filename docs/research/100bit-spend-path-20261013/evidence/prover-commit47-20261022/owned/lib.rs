#![allow(unexpected_cfgs)]
pub mod field;
use field::{WideExact as E,QM31};
pub fn add(x:E,y:E)->E {x.add(y)}
pub fn mul(x:E,y:E)->E {x.mul(y)}
pub fn embedded(q:QM31)->E {E::from_qm31(q)}
pub fn bytes(x:E)->[u8;32] {x.to_le_bytes()}
