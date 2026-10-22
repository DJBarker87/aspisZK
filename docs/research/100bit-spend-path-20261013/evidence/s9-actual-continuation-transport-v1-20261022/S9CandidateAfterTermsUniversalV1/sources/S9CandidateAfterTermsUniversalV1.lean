import S9CandidateAfterTermsComposeV1
import S9CandidateActiveBodyAssemblerV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateAfterTermsUniversalV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev C := AspisR1S9CandidateSideOneTailMapV1.C
abbrev CQ := AspisR1S9CandidateSideOneTailMapV1.CQ
abbrev CA := AspisR1S9CandidateSideOneTailMapV1.CA
abbrev P := AspisR1S9CandidateSideOneTailMapV1.P
abbrev PA := AspisR1S9CandidateSideOneTailMapV1.PA
abbrev MP := AspisR1S9CandidateTermStagesV1.MP

abbrev candidateMapFlow :=
  AspisR1S9CandidateAfterTermsComposeV1.candidateMapFlow

/-- The single branch-independent Result map needed by the active-body
assembler. The only branch split is the source's actual `side = 0` test. -/
theorem candidate_after_terms_result_maps
    (ap1 weights : CA) (iterNext : R) (side : U)
    (q41 q8 q12 q16 : CQ) (low : C) (perm3 : U)
    (hperm3 : Array.index_usize
      _root_.AspisR1S9CandidateHelperV1.weights.PERM 3#usize = .ok perm3)
    (t0 t1 t2 t3 : C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult candidateMapFlow
      (AspisR1S9CandidateBodyTermsV1.candidateAfterTerms ap1 side iterNext
        weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3) =
    @AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP ap1)
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP
        (AspisR1S9CandidateBodyTermsV1.candidateTerms t0 t1 t2 t3))
      side iterNext (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
      (MP low) (AspisR1S9CandidateHelperV1.toP6Q q41)
      (AspisR1S9CandidateHelperV1.toP6Q q16) := by
  by_cases hzero : side = 0#usize
  · subst side
    exact AspisR1S9CandidateAfterTermsComposeV1.candidate_after_terms_side_zero_maps
      ap1 weights iterNext q41 q8 q12 q16 low perm3 t0 t1 t2 t3
  · have hside :=
      AspisR1S9CandidateAfterTermsComposeV1.candidate_after_terms_side_one_maps
        ap1 weights iterNext q41 q8 q12 q16 low perm3 hperm3 t0 t1 t2 t3
    have hone : (1#usize : U) ≠ 0#usize := by decide
    simpa only [AspisR1S9CandidateBodyTermsV1.candidateAfterTerms,
      AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms,
      if_neg hzero, if_neg hone] using hside

/-- The actual successful candidate suffix determines the exact successful P6
assembler suffix on the mapped flow; this is the `hsuffix` premise discharged
for the same source values. -/
theorem candidate_after_terms_success_maps
    (ap1 weights : CA) (iterNext : R) (side : U)
    (q41 q8 q12 q16 : CQ) (low : C) (perm3 : U)
    (hperm3 : Array.index_usize
      _root_.AspisR1S9CandidateHelperV1.weights.PERM 3#usize = .ok perm3)
    (t0 t1 t2 t3 : C) (flow : ControlFlow (R × CA) CA)
    (hsource : AspisR1S9CandidateBodyTermsV1.candidateAfterTerms ap1 side iterNext
      weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 = .ok flow) :
    @AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP ap1)
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP
        (AspisR1S9CandidateBodyTermsV1.candidateTerms t0 t1 t2 t3))
      side iterNext (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
      (MP low) (AspisR1S9CandidateHelperV1.toP6Q q41)
      (AspisR1S9CandidateHelperV1.toP6Q q16) = .ok (candidateMapFlow flow) := by
  have hmap := candidate_after_terms_result_maps ap1 weights iterNext side
    q41 q8 q12 q16 low perm3 hperm3 t0 t1 t2 t3
  rw [hsource] at hmap
  simpa only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] using hmap.symm

#print axioms AspisR1S9CandidateAfterTermsUniversalV1.candidate_after_terms_result_maps
#print axioms AspisR1S9CandidateAfterTermsUniversalV1.candidate_after_terms_success_maps

end AspisR1S9CandidateAfterTermsUniversalV1
