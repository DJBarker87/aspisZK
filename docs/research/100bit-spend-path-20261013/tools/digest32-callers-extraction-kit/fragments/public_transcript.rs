#[inline(always)]
pub fn public_transcript<H: Digest32>(
    public: Public<'_>,
    hash: H,
    c1_root: &[u8; 32],
) -> Result<SemanticTranscript<H>, Error> {
    SemanticTranscript::new(
        hash,
        &public.public_bytes().map_err(|_| Error::Public)?,
        c1_root,
    )
}