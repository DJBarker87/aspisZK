#![no_std]
use aspis_core::Digest32;
use solana_program::hash::hashv;

#[derive(Clone, Copy)]
struct SolanaDigest;
impl aspis_core::Digest32 for SolanaDigest {
    #[inline(always)]
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
        hashv(parts).to_bytes()
    }
}

/// Extraction-only root: the production implementation above is unchanged.
pub fn digest_probe(parts: &[&[u8]]) -> [u8; 32] {
    <SolanaDigest as Digest32>::digest(&SolanaDigest, parts)
}
