

/// Disposable extraction root. Calls the untouched current semantic_round body.
pub fn focused_semantic_round_entry<H: Digest32>(
    prefix: &Prefix<'_>,
    transcript: SemanticTranscript<H>,
    alpha: [QM31; 10],
    running: QM31,
    round: usize,
) -> Result<(QM31, [QM31; 10], SemanticTranscript<H>), Error> {
    semantic_round(prefix, transcript, alpha, running, round)
}
