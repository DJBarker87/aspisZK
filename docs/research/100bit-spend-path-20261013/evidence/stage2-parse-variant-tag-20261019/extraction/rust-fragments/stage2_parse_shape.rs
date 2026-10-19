/// Fixed length, magic, variant S2, zero header tail.
#[inline(never)]
pub fn parse_shape(proof: &[u8]) -> Result<Variant, Error> {
    if proof.len() != compact::PROOF_BYTES
        || &proof[..8] != compact::MAGIC
        || proof[8] != Variant::S2.tag()
        || proof[9..16].iter().any(|&x| x != 0)
    {
        return Err(Error::Parse);
    }
    Ok(Variant::S2)
}