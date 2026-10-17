#[cfg(not(feature = "prover"))]
fn semantic_rounds<H: Digest32>(prefix: &Prefix<'_>, mut transcript: SemanticTranscript<H>) -> Result<(QM31, [QM31; 10], SemanticTranscript<H>), Error> {
    let mut running = prefix.validated_record(14)?.decode_k::<1>(0)?[0];
    let mut alpha = [QM31::ZERO; 10];
    #[cfg(feature = "prover")]
    let mut round_checks = [[QM31::ZERO; 3]; 10];
    {
        let round = 0usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 1usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 2usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 3usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 4usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 5usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 6usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 7usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 8usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 9usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    Ok((running, alpha, transcript))
}