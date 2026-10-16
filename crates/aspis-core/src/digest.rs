//! Statically selected digest backend for the R1 verifier path.
//!
//! This interface specifies the call shape, not purity, SHA-256 semantics,
//! syscall cost, or a source-refinement theorem for an implementation.

pub trait Digest32: Copy {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32];
}

/// Compatibility for retained R0 and host/prover function-pointer APIs.
/// The admitted R1 program supplies its concrete syscall backend instead.
#[derive(Clone, Copy)]
pub struct LegacyHashFn(pub crate::HashFn);

impl Digest32 for LegacyHashFn {
    #[inline]
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
        (self.0)(parts)
    }
}
