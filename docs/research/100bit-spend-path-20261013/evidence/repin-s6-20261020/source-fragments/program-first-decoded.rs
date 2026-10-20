/// Reuse the adapter's decoded statement while hashing its original bytes.
/// The immutable account-data borrow keeps this value tied to those same bytes.
#[inline(never)]
fn first_decoded(public:aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize)->Result<Vec<u8>,ProgramError>{
    verifier::tx1(public,public_bytes,proof,k,SolanaDigest,observer()).map_err(error)
}