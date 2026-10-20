#[inline(never)]
pub fn verify_observed<H: Digest32>(public: Public<'_>, bytes: &[u8], hash: H, obs: crate::verifier::Observer) -> Result<Verified<H>, Error> {
    let prefix = Prefix::parse(bytes)?;
    mark(obs, 0);
    let mut transcript = public_transcript(public, hash, prefix.c1_root)?;
    let challenges = wire::begin(&prefix, &mut transcript)?;
    mark(obs, 1);
    verify_finish(public, prefix, transcript, challenges, obs)
}