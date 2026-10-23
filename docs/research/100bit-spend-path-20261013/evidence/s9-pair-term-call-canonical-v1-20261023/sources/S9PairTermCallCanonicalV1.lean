import S9PairMixedProductCanonicalV1
import S9PairQuarterTermCanonicalV1
import S9PairPrefixAllCallsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairTermCallCanonicalV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PU := Std.Usize

/-- A term value from one exact Pair callback invocation is canonical on the
same successful input read. The mixed product is canonicalized by the actual
mixed-operation totality bridge; the quarter multiplication uses its own
actual scalar-product totality bridge. -/
theorem pair_term_call_canonical
    (ap1 : Array PW (4#usize)) (high : Array PQ (4#usize)) (i : PU)
    (call : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1 high i)
    (hap1 : ∀ (j : PU) (v : AspisR1S9HelperP6.field.WideExact),
      (Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
            AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)) j = .ok v) →
      AspisR1S9HighTermsTraceV1.canonicalW v) :
    AspisR1S9HighTermsTraceV1.canonicalW
      (AspisR1S9PairCallerStepV1.toP6W call.term) := by
  have hproduct :=
    AspisR1S9PairMixedProductCanonicalV1.pair_mixed_success_product_canonical
      ap1 call.perm call.input call.coefficient call.product call.inputRead hap1
      call.mixedSuccess
  exact AspisR1S9PairQuarterTermCanonicalV1.pair_quarter_term_success_canonical
    call.product call.term hproduct call.quarterSuccess

#print axioms pair_term_call_canonical

end AspisR1S9PairTermCallCanonicalV1
