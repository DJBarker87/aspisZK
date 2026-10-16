pub fn begin<H: Digest32>(
    prefix: &Prefix<'_>,
    transcript: &mut SemanticTranscript<H>,
) -> Result<Challenges, Error> {
    let lambda = transcript.semantic_validated(prefix.validated_record(0)?)?;
    let chi = transcript.semantic_validated(prefix.validated_record(1)?)?;
    let theta = transcript.semantic_validated(prefix.validated_record(2)?)?;
    let mut zc = [QM31::ZERO; 10];
    for (i, value) in zc.iter_mut().enumerate() {
        *value = transcript.semantic_validated(prefix.validated_record(3 + i as u8)?)?;
    }
    let mu = transcript.semantic_validated(prefix.validated_record(13)?)?;
    let eta = transcript.semantic_validated(prefix.validated_record(14)?)?;
    Ok(Challenges {
        lambda,
        chi,
        theta,
        zc,
        mu,
        eta,
    })
}
