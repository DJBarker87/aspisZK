fn S2K_header(afterstate: &PoolV1PairVerifiedAfterstateV1) -> [u8;688] {
    let mut output = [0u8; POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC);
    output[4] = POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION;
    output[5] = super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[7] = 1;
    output[8..16].copy_from_slice(&afterstate.next_pair_index.to_le_bytes());
    output[16..48].copy_from_slice(&encode_digest_canonical(&afterstate.next_root));
    output
}
