pub fn tx2_authenticated<H: Digest32>(public_bytes: &[u8], proof: &[u8], checkpoint: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    parse_shape(proof)?;
    mark(obs, Phase::Parsed);
    tx2_common(public_bytes, proof, checkpoint, hash, obs)
}
