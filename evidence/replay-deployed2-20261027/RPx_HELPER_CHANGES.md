# RPx helper repair

Authorized by the lead correction. All binders and the existential conclusion are unchanged. The original helper premise is ill-typed in the pinned cohort.

Before:
```lean
FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)
```
After:
```lean
FinishModel.finish R B D pub pre before challenges
  (RPz7_PhaseIso.observerToFirst obs) = ok (.Ok out)
```

The matching call to S1SemanticFinishBounds.finish_success receives the same transported observer. The existing observerToFirst is Option.map of contravariant callbackToFirst, defined by toVerifier. Its invertibility is proved by first_roundtrip_RPz7, verifier_roundtrip_RPz7, callback_first_roundtrip_RPz7, callback_verifier_roundtrip_RPz7, observer_first_roundtrip_RPz7 and observer_verifier_roundtrip_RPz7 in RPz7_PhaseIso. No carrier equality or new isomorphism is assumed. The helper uses observerToFirst explicitly; the successful-finish proof is applied directly on its retained carrier. The none observer at the direct descendant reduces to none.

All other descendant declarations retain their statements and proof bodies, with imports redirected to the fresh repaired closure. Root declaration namespace becomes AspisR1.RPx_Deployed; root type preservation remains subject to the mandatory byte gate.

## Complete original helper statement

```lean
theorem terminal_comparison_of_finish_success
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (out : r1_semantic.Verified H)
    (hfinish : FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)) :
    ∃ running afterRounds terminal mask16 mask10 claim0 claim27 mask
        etaTerminal masked extra28,
      RoundModel.rounds R D pre before = ok (.Ok (running, out.alpha, afterRounds)) ∧
      B.terminal pub out.claims out.alpha challenges = ok (.Ok terminal) ∧
      B.fromFn 16#usize (FinishModel.closureFn9 D) out.claims = ok mask16 ∧
      B.fromFn 10#usize (FinishModel.closureFn5 D) out.claims = ok mask10 ∧
      Array.index_usize out.claims 0#usize = ok claim0 ∧
      Array.index_usize claim0 27#usize = ok claim27 ∧
      B.mask mask16 mask10 claim27 out.alpha = ok mask ∧
      B.mul challenges.eta terminal = ok etaTerminal ∧
      B.add mask etaTerminal = ok masked ∧
      Array.index_usize out.extra 28#usize = ok extra28 ∧
      B.add masked extra28 = ok running
```

## Complete repaired helper statement

```lean
theorem terminal_comparison_of_finish_success
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (out : r1_semantic.Verified H)
    (hfinish : FinishModel.finish R B D pub pre before challenges (RPz7_PhaseIso.observerToFirst obs) = ok (.Ok out)) :
    ∃ running afterRounds terminal mask16 mask10 claim0 claim27 mask
        etaTerminal masked extra28,
      RoundModel.rounds R D pre before = ok (.Ok (running, out.alpha, afterRounds)) ∧
      B.terminal pub out.claims out.alpha challenges = ok (.Ok terminal) ∧
      B.fromFn 16#usize (FinishModel.closureFn9 D) out.claims = ok mask16 ∧
      B.fromFn 10#usize (FinishModel.closureFn5 D) out.claims = ok mask10 ∧
      Array.index_usize out.claims 0#usize = ok claim0 ∧
      Array.index_usize claim0 27#usize = ok claim27 ∧
      B.mask mask16 mask10 claim27 out.alpha = ok mask ∧
      B.mul challenges.eta terminal = ok etaTerminal ∧
      B.add mask etaTerminal = ok masked ∧
      Array.index_usize out.extra 28#usize = ok extra28 ∧
      B.add masked extra28 = ok running
```
