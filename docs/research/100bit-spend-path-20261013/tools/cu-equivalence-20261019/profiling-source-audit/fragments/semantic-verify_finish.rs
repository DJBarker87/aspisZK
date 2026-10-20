fn verify_finish<H: Digest32>(public: Public<'_>, prefix: Prefix<'_>, mut transcript: SemanticTranscript<H>, challenges: Challenges, obs: crate::verifier::Observer) -> Result<Verified<H>, Error> {
    #[cfg(not(feature = "prover"))]
    let (running, alpha, mut transcript) = semantic_rounds(&prefix, transcript)?;
    #[cfg(feature = "prover")]
    let (running, alpha, mut transcript, round_checks) = semantic_rounds(&prefix, transcript)?;
    mark(obs, 2);
    let claims = claims(&prefix)?;
    let original_challenges = aspis_core::state_only_prefix::r0::Challenges {
        lambda: challenges.lambda,
        chi: challenges.chi,
        theta: challenges.theta,
        zc: challenges.zc,
        mu: challenges.mu,
        eta: challenges.eta,
    };
    let terminal = public
        .terminal_qm31(&claims, &alpha, &original_challenges)
        .map_err(|_| Error::Public)?;
    mark(obs, 3);
    let mask = aspis_core::state_only_hiding::state_only_selected_mask_value(
        &core::array::from_fn(|i| claims[0][i]),
        &core::array::from_fn(|i| claims[0][16 + i]),
        claims[0][27],
        &alpha,
    );
    let extra = prefix.validated_record(25)?.decode_k::<29>(87)?;
    let masked_terminal = mask.add(challenges.eta.mul(terminal)).add(extra[28]);
    if running != masked_terminal {
        return Err(Error::Terminal);
    }
    mark(obs, 4);
    let state_before_z0 = transcript.state();
    let z0 = transcript.circle_validated(prefix.validated_record(25)?)?;
    let before_z1 = prefix.validated_record(26)?.decode_k::<29>(0)?;
    let z1 = transcript.circle_validated(prefix.validated_record(26)?)?;
    mark(obs, 5);
    #[cfg(feature = "prover")]
    {
        for (i, x) in [z0.x, z0.y, z1.x, z1.y].into_iter().enumerate() {
            crate::trace::value(3, i, aspis_core::field::WideExact::from_qm31(x));
        }
        for (i, x) in challenges.with_alphas(&alpha).into_iter().enumerate() {
            crate::trace::value(0, i, x);
        }
        for (i, row) in round_checks.iter().enumerate() {
            for (j, x) in row.iter().enumerate() {
                crate::trace::value(1, 3 * i + j, aspis_core::field::WideExact::from_qm31(*x));
            }
        }
        crate::trace::value(2, 0, aspis_core::field::WideExact::from_qm31(terminal));
        crate::trace::value(
            2,
            1,
            aspis_core::field::WideExact::from_qm31(masked_terminal),
        );
    }
    if z0 == z1 {
        return Err(Error::EqualCirclePoints);
    }
    Ok(Verified {
        roots: [*prefix.c1_root, prefix.payload(2)?.try_into().unwrap()],
        challenges,
        alpha,
        claims,
        extra,
        before_z1,
        state_before_z0,
        z: [z0, z1],
        transcript,
        #[cfg(feature = "prover")]
        round_checks,
        #[cfg(feature = "prover")]
        terminal,
        #[cfg(feature = "prover")]
        masked_terminal,
    })
}