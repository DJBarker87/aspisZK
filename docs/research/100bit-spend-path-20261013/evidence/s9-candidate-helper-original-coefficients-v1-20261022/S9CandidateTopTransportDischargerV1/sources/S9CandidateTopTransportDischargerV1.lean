import S9CandidateAfterTermsUniversalV1
import S9CandidateTopHelperMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateTopTransportDischargerV1

open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateFoldMapPrimitivesV1
open AspisR1S9CandidateHelperLoopMapV1
open AspisR1S9CandidateTopHelperMapV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev CArray := Array CW (4#usize)

/-- Discharge the loop mapper's only missing premise from the same successful
candidate suffix execution. The result conversion is definitional because the
loop and universal suffix modules use the same fieldwise map on `ControlFlow`.
-/
theorem candidate_suffix_transport_of_success
    (ap1 : CArray) : CandidateSuffixTransport ap1 := by
  intro side iterNext weights flow q41 q8 q12 q16 low perm3 t0 t1 t2 t3 hperm hsource
  have h := AspisR1S9CandidateAfterTermsUniversalV1.candidate_after_terms_success_maps
    ap1 weights iterNext side q41 q8 q12 q16 low perm3 hperm t0 t1 t2 t3 flow hsource
  have hflow :
      AspisR1S9CandidateAfterTermsUniversalV1.candidateMapFlow flow =
        AspisR1S9CandidateHelperLoopMapV1.mapCandidateFlow flow := by
    cases flow with
    | done a => rfl
    | cont pair => cases pair; rfl
  have h' := h
  dsimp only [AspisR1S9CandidateAfterTermsUniversalV1.MP] at h'
  rw [hflow] at h'
  exact h'

/-- The actual top-level candidate success maps to the P6 top-level helper
once its real canonical-read obligations are supplied. The suffix transport
is constructed from the actual candidate Result rather than assumed.
-/
theorem candidate_top_success_maps_to_p6
    (ap0 ap1 : CArray) (extra : Array CQ (2#usize)) (output : CArray)
    (htop : _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights
      ap0 ap1 extra = .ok output)
    (hextra : ∀ (j : U) (x : CQ), Array.index_usize extra j = .ok x →
      AspisR1S9CandidateHighArraySemanticsV1.CanonicalP6
        (AspisR1S9CandidateHelperV1.toP6Q x))
    (hap1 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap1) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x) :
    @AspisR1S9HelperP6.weights.factored_s2_libra_weights
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) =
      .ok (mapArray AspisR1S9CandidateHelperV1.toP6W output) := by
  exact AspisR1S9CandidateTopHelperMapV1.candidate_top_success_maps_to_p6
    ap0 ap1 extra output htop hextra hap1
    (candidate_suffix_transport_of_success ap1)

#print axioms candidate_suffix_transport_of_success
#print axioms candidate_top_success_maps_to_p6

end AspisR1S9CandidateTopTransportDischargerV1
