import S9PairWideSourceCarrierV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9PairWideMulExactV1
abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev SW := AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact
abbrev toSource := AspisR1S9PairWideSourceCarrierV1.pairToSourceW
abbrev toPair := AspisR1S9WideMulPairHelperBridgeV1.srcToPairW
abbrev toHelper := AspisR1S9PairCallerStepV1.toP6W
abbrev toCurrent := AspisR1S9WideFullCurrentSourceV1.toCurrentWide

private theorem source_output_current (x : SW) :
    AspisR1S9CurrentFieldOpsV1.toE (toHelper (toPair x)) = toCurrent x := by
  cases x <;> rfl

/-- Exact field semantics and canonicality of this actual Pair multiplication
follow from constructive totality of its pinned raw source operation. -/
theorem pair_mul_success_exact (x y product : PW)
    (hx : AspisR1S9CurrentFieldOpsV1.Canonical (toHelper x))
    (hy : AspisR1S9CurrentFieldOpsV1.Canonical (toHelper y))
    (hcall : AspisR1S9PairCallerStepV1.field.WideExact.mul x y = .ok product) :
    ∃ sourceOut : SW,
      AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul
        (toSource x) (toSource y) = .ok sourceOut ∧
      toHelper product = toHelper (toPair sourceOut) ∧
      AspisR1S9CurrentFieldOpsV1.Canonical (toHelper product) ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9CurrentFieldOpsV1.toE (toHelper product)) =
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9CurrentFieldOpsV1.toE (toHelper x)) *
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9CurrentFieldOpsV1.toE (toHelper y)) := by
  have hsx := AspisR1S9PairWideSourceCarrierV1.pair_canonical_to_source x hx
  have hsy := AspisR1S9PairWideSourceCarrierV1.pair_canonical_to_source y hy
  obtain ⟨out,hs,hcan,hdecode⟩ :=
    AspisR1S9SourceWideMulTotalExactV1.source_wide_mul_total_exact
      (toSource x) (toSource y) hsx hsy
  have hm := AspisR1S9WideMulPairHelperBridgeV1.pair_mul_matches_source_mul
    (toSource x) (toSource y) hsx.1 hsx.2 hsy.1 hsy.2
  rw [AspisR1S9PairWideSourceCarrierV1.source_pair_inverse x,
    AspisR1S9PairWideSourceCarrierV1.source_pair_inverse y,hcall,hs] at hm
  have hp : toHelper product = toHelper (toPair out) := by
    change Result.ok (toHelper product) = Result.ok (toHelper (toPair out)) at hm
    exact Result.ok.inj hm
  have hc : AspisR1S9CurrentFieldOpsV1.Canonical (toHelper product) := by
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE (toHelper product))
    rw [hp,source_output_current]
    exact hcan
  refine ⟨out,hs,hp,hc,?_⟩
  rw [hp,source_output_current]
  change AspisR1CurrentWide.Proof.decodeWide
    (AspisR1S9WideFullCurrentSourceV1.toCurrentWide out) =
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9WideFullCurrentSourceV1.toCurrentWide
          (AspisR1S9PairWideSourceCarrierV1.pairToSourceW x)) *
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9WideFullCurrentSourceV1.toCurrentWide
          (AspisR1S9PairWideSourceCarrierV1.pairToSourceW y)) at hdecode
  rw [AspisR1S9PairWideSourceCarrierV1.source_current_matches_helper x,
    AspisR1S9PairWideSourceCarrierV1.source_current_matches_helper y] at hdecode
  exact hdecode

#print axioms pair_mul_success_exact
end AspisR1S9PairWideMulExactV1
