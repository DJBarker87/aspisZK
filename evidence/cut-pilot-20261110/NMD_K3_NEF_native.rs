use super::*;
#[kani::proof]
fn NEF_none_control() { assert!(None::<fn(Phase)>.is_none()); }
