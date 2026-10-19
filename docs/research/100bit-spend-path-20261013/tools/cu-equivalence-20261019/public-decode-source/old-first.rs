#[inline(never)]
fn first(public_bytes:&[u8],proof:&[u8],k:usize)->Result<Vec<u8>,ProgramError>{
    let statement=decode_pool_v1_pair_forest_terminal_statement_v1(public_bytes).map_err(|_|ProgramError::InvalidAccountData)?;
    let public=statement.semantic_public();
    verifier::tx1(public,public_bytes,proof,k,SolanaDigest,observer()).map_err(error)
}