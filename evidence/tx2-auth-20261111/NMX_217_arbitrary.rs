// Kani-only type support for the complete native M31 memory representation.
// Every u32 bit pattern is generated; no canonicality or success restriction.
use super::M31;
impl kani::Arbitrary for M31 {
    fn any()->Self { M31(kani::any::<u32>()) }
}
