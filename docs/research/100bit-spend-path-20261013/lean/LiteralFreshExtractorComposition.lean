import LiteralBudgetEnvelope

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.LiteralFreshExtractorComposition

open AspisR1.PerAttemptEnvelope

/-- A one-attempt event-composition lemma. `pFailureCover` records the
averaged deterministic implication: every accepted failure is covered by the
33-round fresh challenge classifier event or by extractor abort. The input
`pHitBound` is supplied by LiteralFreshAttemptBound.hitMass_le; the
extractor bound is supplied by the fixed-input byte-bank theorem under the
protocol's explicit decoded/semantic assumptions. No shared-ROM/query claim is
made here. -/
theorem one_attempt_failure_lt
    (pHit pExtractor pFailure : ℚ)
    (pHitBound : pHit ≤ 33 * B)
    (pFailureCover : pFailure ≤ pHit + pExtractor)
    (pExtractorBound : pExtractor < (1 / (2 : ℚ)^126)) :
    pFailure < 1 / (2 : ℚ)^100 := by
  have hslack : 33 * B + (1 / (2 : ℚ)^126) < 1 / (2 : ℚ)^100 := by
    unfold B
    norm_num
  calc
    pFailure ≤ pHit + pExtractor := pFailureCover
    _ ≤ 33 * B + pExtractor := by
      simpa [add_comm] using add_le_add_right pHitBound pExtractor
    _ < 33 * B + (1 / (2 : ℚ)^126) := by
      simpa [add_comm] using add_lt_add_right pExtractorBound (33 * B)
    _ < 1 / (2 : ℚ)^100 := hslack

#print axioms one_attempt_failure_lt
end AspisR1.LiteralFreshExtractorComposition
