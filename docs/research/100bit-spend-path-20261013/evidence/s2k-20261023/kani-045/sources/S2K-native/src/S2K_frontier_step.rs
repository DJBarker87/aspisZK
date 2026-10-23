fn frontier_step(mut output: [u8;688], level: usize, node: &aspis_statement::poseidon2::Digest) -> [u8;688] {
        let start = 48 + 32 * level;
        output[start..start + 32].copy_from_slice(&encode_digest_canonical(node));
    output
}
