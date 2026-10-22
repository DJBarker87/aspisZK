import S9CandidateAfterTermsTotalityV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateAfterTermsContTotalV1

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

/-- Specialize the Result-map inversion to the loop's continuation result.
Besides candidate suffix success, this exposes the exact same next iterator
and mapped output array, which lets the caller transfer cell invariants from
the P6 tail result. -/
theorem candidate_after_terms_cont_total_of_p6_success
    (ap1 weights : CA) (iterNext : R) (side : U)
    (q41 q8 q12 q16 : CQ) (low : C) (perm3 : U)
    (hperm3 : Array.index_usize AspisR1S9CandidateHelperV1.weights.PERM
      3#usize = .ok perm3)
    (t0 t1 t2 t3 : C) (p6out : PA)
    (hp6 : @AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP ap1)
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP
        (AspisR1S9CandidateBodyTermsV1.candidateTerms t0 t1 t2 t3))
      side iterNext (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
      (MP low) (AspisR1S9CandidateHelperV1.toP6Q q41)
      (AspisR1S9CandidateHelperV1.toP6Q q16) = .ok (.cont (iterNext,p6out))) :
    ∃ cout : CA,
      AspisR1S9CandidateBodyTermsV1.candidateAfterTerms ap1 side iterNext
        weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 = .ok (.cont (iterNext,cout)) ∧
      AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP cout = p6out := by
  obtain ⟨flow,hsource,hmapped⟩ :=
    AspisR1S9CandidateAfterTermsTotalityV1.candidate_after_terms_total_of_p6_success
      ap1 weights iterNext side q41 q8 q12 q16 low perm3 hperm3
      t0 t1 t2 t3 (.cont (iterNext,p6out)) hp6
  cases flow with
  | cont pair =>
      rcases pair with ⟨iterOut,cout⟩
      change AspisR1S9CandidateAfterTermsComposeV1.candidateMapFlow
          (.cont (iterOut,cout)) = .cont (iterNext,p6out) at hmapped
      simp only [AspisR1S9CandidateAfterTermsComposeV1.candidateMapFlow] at hmapped
      injection hmapped with hpair
      have hiter := congrArg Prod.fst hpair
      have harray := congrArg Prod.snd hpair
      change iterOut = iterNext at hiter
      change AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP cout = p6out at harray
      subst iterOut
      exact ⟨cout,hsource,harray⟩
  | done cout =>
      change AspisR1S9CandidateAfterTermsComposeV1.candidateMapFlow
          (.done cout) = .cont (iterNext,p6out) at hmapped
      simp only [AspisR1S9CandidateAfterTermsComposeV1.candidateMapFlow] at hmapped
      cases hmapped

#print axioms candidate_after_terms_cont_total_of_p6_success

end AspisR1S9CandidateAfterTermsContTotalV1
