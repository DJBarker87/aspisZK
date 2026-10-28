// Scratch-only input generation. Every field is an independent arbitrary u32;
// canonicality is asserted/assumed only in the caller's explicit domain.
impl kani::Arbitrary for crate::field::QM31 {
 fn any()->Self{
  use crate::field::{M31,CM31};
  Self{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}
 }
}
