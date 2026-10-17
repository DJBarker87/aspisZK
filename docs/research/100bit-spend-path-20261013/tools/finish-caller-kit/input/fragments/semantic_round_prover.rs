#[cfg(feature = "prover")]
fn semantic_round<H: Digest32>(prefix: &Prefix<'_>, mut transcript: SemanticTranscript<H>, mut alpha: [QM31; 10], mut running: QM31, round: usize, mut round_checks: [[QM31; 3]; 10]) -> Result<(QM31, [QM31; 10], SemanticTranscript<H>, [[QM31; 3]; 10]), Error> {
        let row = 15 + round as u8;
        let polynomial = prefix.validated_record(row)?.decode_k::<28>(0)?;
        let boundary = semantic_boundary(&polynomial);
        if boundary != running {
            return Err(Error::Boundary { round });
        }
        alpha[round] = transcript.semantic_validated(prefix.validated_record(row)?)?;
        let value = semantic_value(&polynomial, &alpha, round);
        #[cfg(feature = "prover")]
        {
            round_checks[round] = [running, boundary, value];
        }
        running = value;
    Ok((running, alpha, transcript, round_checks))
}