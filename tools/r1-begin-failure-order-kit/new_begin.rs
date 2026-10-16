pub fn begin<H: Digest32>(
    prefix: &Prefix<'_>,
    transcript: &mut SemanticTranscript<H>,
) -> Result<Challenges, Error> {
    let lambda = transcript.semantic_validated(prefix.validated_record(0)?)?;
    let chi = transcript.semantic_validated(prefix.validated_record(1)?)?;
    let theta = transcript.semantic_validated(prefix.validated_record(2)?)?;
    let mut zc = [QM31::ZERO; 10];
    zc[0] = transcript.semantic_validated(prefix.validated_record(3)?)?;
    zc[1] = transcript.semantic_validated(prefix.validated_record(4)?)?;
    zc[2] = transcript.semantic_validated(prefix.validated_record(5)?)?;
    zc[3] = transcript.semantic_validated(prefix.validated_record(6)?)?;
    zc[4] = transcript.semantic_validated(prefix.validated_record(7)?)?;
    zc[5] = transcript.semantic_validated(prefix.validated_record(8)?)?;
    zc[6] = transcript.semantic_validated(prefix.validated_record(9)?)?;
    zc[7] = transcript.semantic_validated(prefix.validated_record(10)?)?;
    zc[8] = transcript.semantic_validated(prefix.validated_record(11)?)?;
    zc[9] = transcript.semantic_validated(prefix.validated_record(12)?)?;
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
