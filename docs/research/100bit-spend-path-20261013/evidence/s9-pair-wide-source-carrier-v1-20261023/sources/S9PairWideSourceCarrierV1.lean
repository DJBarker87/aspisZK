import S9WideMulPairHelperBridgeV1
import S9SourceWideMulTotalExactV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9PairWideSourceCarrierV1
abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev SW := AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact

def pairToSourceW (x : PW) : SW :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem source_pair_inverse (x : PW) :
    AspisR1S9WideMulPairHelperBridgeV1.srcToPairW (pairToSourceW x) = x := by
  cases x <;> rfl

theorem source_current_matches_helper (x : PW) :
    AspisR1S9WideFullCurrentSourceV1.toCurrentWide (pairToSourceW x) =
      AspisR1S9CurrentFieldOpsV1.toE (AspisR1S9PairCallerStepV1.toP6W x) := by
  cases x <;> rfl

/-- The eight canonical source coordinates are exactly those of this Pair value. -/
theorem pair_canonical_to_source (x : PW)
    (h : AspisR1S9CurrentFieldOpsV1.Canonical
      (AspisR1S9PairCallerStepV1.toP6W x)) :
    AspisR1S9SourceWideMulTotalExactV1.Canonical (pairToSourceW x) := by
  exact h

#print axioms source_pair_inverse
#print axioms source_current_matches_helper
#print axioms pair_canonical_to_source
end AspisR1S9PairWideSourceCarrierV1
