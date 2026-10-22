import S9CandidateAfterTermsUniversalV1
import S9CandidateAfterTermsComposeV1
import S9CandidateActiveBodyAssemblerV1
import S9CandidateBodyTermsV1
import S9CandidateTermStagesComposeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateAfterTermsTotalityV1

open AspisR1S9CandidateBodyTermsV1
open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateTermStagesComposeV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev C := AspisR1S9CandidateSideOneTailMapV1.C
abbrev CQ := AspisR1S9CandidateSideOneTailMapV1.CQ
abbrev CA := AspisR1S9CandidateSideOneTailMapV1.CA
abbrev PA := AspisR1S9CandidateSideOneTailMapV1.PA
abbrev MP := AspisR1S9CandidateTermStagesV1.MP

private theorem mapResult_ok_inv {A B : Type} (f : A → B) (r : Result A) (b : B)
    (hmap : AspisR1S9CandidateFoldMapPrimitivesV1.mapResult f r = .ok b) :
    ∃ a, r = .ok a ∧ f a = b := by
  cases r with
  | ok a => exact ⟨a, rfl, Result.ok.inj hmap⟩
  | fail e => simp [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] at hmap
  | div => simp [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] at hmap

/-- If the selected P6 post-terms computation succeeds for the exact mapped
candidate values, the candidate's corresponding post-terms Result succeeds.
This reverses the already-checked full-Result map, so failure and divergence
are ruled out by the selected `.ok` result rather than a candidate success
premise. -/
theorem candidate_after_terms_total_of_p6_success
    (ap1 weights : CA) (iterNext : R) (side : U)
    (q41 q8 q12 q16 : CQ) (low : C) (perm3 : U)
    (hperm3 : Array.index_usize AspisR1S9CandidateHelperV1.weights.PERM
      3#usize = .ok perm3)
    (t0 t1 t2 t3 : C)
    (p6flow : ControlFlow (R × PA) PA)
    (hp6 : @AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP ap1)
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP
        (AspisR1S9CandidateBodyTermsV1.candidateTerms t0 t1 t2 t3))
      side iterNext (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
      (MP low) (AspisR1S9CandidateHelperV1.toP6Q q41)
      (AspisR1S9CandidateHelperV1.toP6Q q16) = .ok p6flow) :
    ∃ flow : ControlFlow (R × CA) CA,
      AspisR1S9CandidateBodyTermsV1.candidateAfterTerms ap1 side iterNext
        weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 = .ok flow ∧
      AspisR1S9CandidateAfterTermsComposeV1.candidateMapFlow flow = p6flow := by
  have hmap := AspisR1S9CandidateAfterTermsUniversalV1.candidate_after_terms_result_maps
    ap1 weights iterNext side q41 q8 q12 q16 low perm3 hperm3 t0 t1 t2 t3
  rw [hp6] at hmap
  obtain ⟨flow,hcandidate,hflow⟩ := mapResult_ok_inv
    AspisR1S9CandidateAfterTermsComposeV1.candidateMapFlow
    (AspisR1S9CandidateBodyTermsV1.candidateAfterTerms ap1 side iterNext
      weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3) p6flow hmap
  exact ⟨flow,hcandidate,hflow⟩

#print axioms candidate_after_terms_total_of_p6_success

end AspisR1S9CandidateAfterTermsTotalityV1
