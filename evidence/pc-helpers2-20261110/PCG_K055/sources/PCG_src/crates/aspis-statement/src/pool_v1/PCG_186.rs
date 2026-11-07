use super::*;
// The actual frozen closure, applied for one Iterator::all iteration.
fn predicate(limb:&M31)->bool{limb.0<P}
#[kani::proof]
fn arbitrary_step(){let prefix:bool=kani::any();let word:u32=kani::any();let item=[M31(word)];let got=prefix&&item.iter().all(predicate);let expected=prefix&&(u64::from(word)<2147483647);assert!((got==expected)!=cfg!(PCG_NEG_CANONICAL));}
