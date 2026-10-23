import S9WideMulPairHelperBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairWideMulSameCallV1

abbrev Src := AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact
abbrev PairW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev HelperW := AspisR1S9HelperP6.field.WideExact

/-- A successful wide multiplication already observed in the Pair execution
has a corresponding successful execution of the pinned transparent source
`WideExact.mul`. The source result is obtained by inverting the equality of
full `Result` values; this theorem does not assume a second success. -/
theorem same_successful_pair_call_has_source_result
    (x y : Src) (z : PairW)
    (hx0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM x.c0)))
    (hx1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM x.c1)))
    (hy0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM y.c0)))
    (hy1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM y.c1)))
    (hcall : AspisR1S9PairCallerStepV1.field.WideExact.mul
      (AspisR1S9WideMulPairHelperBridgeV1.srcToPairW x)
      (AspisR1S9WideMulPairHelperBridgeV1.srcToPairW y) = .ok z) :
    ∃ sourceOut,
      AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y = .ok sourceOut ∧
      AspisR1S9PairCallerStepV1.toP6W z =
        AspisR1S9PairCallerStepV1.toP6W
          (AspisR1S9WideMulPairHelperBridgeV1.srcToPairW sourceOut) := by
  have hsame := AspisR1S9WideMulPairHelperBridgeV1.pair_mul_matches_source_mul
    x y hx0 hx1 hy0 hy1
  rw [hcall] at hsame
  cases hsource : AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y with
  | ok sourceOut =>
      rw [hsource] at hsame
      have hmapped : Result.ok (AspisR1S9PairCallerStepV1.toP6W z) =
          Result.ok (AspisR1S9PairCallerStepV1.toP6W
            (AspisR1S9WideMulPairHelperBridgeV1.srcToPairW sourceOut)) := by
        simpa only [AspisR1S9PairCallerStepOperationBridgeV1.mapResult] using hsame
      exact ⟨sourceOut, rfl, Result.ok.inj hmapped⟩
  | fail e =>
      rw [hsource] at hsame
      simp only [AspisR1S9PairCallerStepOperationBridgeV1.mapResult] at hsame
      cases hsame
  | div =>
      rw [hsource] at hsame
      simp only [AspisR1S9PairCallerStepOperationBridgeV1.mapResult] at hsame
      cases hsame

#print axioms same_successful_pair_call_has_source_result

end AspisR1S9PairWideMulSameCallV1
