import S9CandidateTermStagesComposeV1
import S9CandidateTermSumsFlatBindV2
import S9CandidateTailFlatBindV1
import S9CandidateSideZeroTailMapV1
import S9CandidateSideOneTailMapV4
import S9CandidateActiveBodyAssemblerV1
import S9CandidateBodyTermsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1S9CandidateTermStagesComposeV1

namespace AspisR1S9CandidateAfterTermsComposeV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev C := AspisR1S9CandidateSideOneTailMapV1.C
abbrev CQ := AspisR1S9CandidateSideOneTailMapV1.CQ
abbrev CA := AspisR1S9CandidateSideOneTailMapV1.CA
abbrev P := AspisR1S9CandidateSideOneTailMapV1.P
abbrev PA := AspisR1S9CandidateSideOneTailMapV1.PA
abbrev MP := AspisR1S9CandidateTermStagesV1.MP
abbrev Mout := AspisR1S9CandidateTermStagesV1.Mout

def candidateMapFlow (x : ControlFlow (R × CA) CA) : ControlFlow (R × PA) PA :=
  match x with
  | .cont (r,a) => .cont (r,
      AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP a)
  | .done a => .done (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP a)

private theorem zeroTailFlowMap
    (weights : CA) (low first3 all : C) (q16 : CQ) (iterNext : R) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult candidateMapFlow
      (do
        let a ← AspisR1S9CandidateSideZeroTailMapV1.candidateSideZeroTail
          weights low first3 all q16
        .ok (.cont (iterNext,a))) =
      (do
        let a ← AspisR1.S9SideZeroTailRootV1.sideZeroTail
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
          (MP low) (MP first3) (MP all)
          (AspisR1S9CandidateHelperV1.toP6Q q16)
        .ok (.cont (iterNext,a))) := by
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr candidateMapFlow
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP)
    (AspisR1S9CandidateSideZeroTailMapV1.candidateSideZeroTail
      weights low first3 all q16)
    (AspisR1.S9SideZeroTailRootV1.sideZeroTail
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
      (MP low) (MP first3) (MP all)
      (AspisR1S9CandidateHelperV1.toP6Q q16))
    (fun a => .ok (.cont (iterNext,a)))
    (fun a => .ok (.cont (iterNext,a)))
    (AspisR1S9CandidateSideZeroTailMapV1.candidate_side_zero_tail_maps
      weights low first3 all q16)
    (by intro a; rfl)

private theorem oneTailFlowMap
    (weights ap1 : CA) (low all first2 : C) (q41 q16 : CQ)
    (perm3 : U) (hperm3 : Array.index_usize
      _root_.AspisR1S9CandidateHelperV1.weights.PERM 3#usize = .ok perm3)
    (iterNext : R) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult candidateMapFlow
      (do
        let a ← AspisR1S9CandidateSideOneTailMapV4.candidateAfterOld
          weights ap1 low all first2 q41 q16 perm3
        .ok (.cont (iterNext,a))) =
      (do
        let a ← AspisR1S9CandidateSideOneTailMapV4.p6AfterOld
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP ap1)
          (MP low) (MP all) (MP first2)
          (AspisR1S9CandidateHelperV1.toP6Q q41)
          (AspisR1S9CandidateHelperV1.toP6Q q16)
        .ok (.cont (iterNext,a))) := by
  obtain ⟨_, htail⟩ :=
    AspisR1S9CandidateSideOneTailMapV4.candidate_side_one_from_bound_perm
      weights ap1 low all first2 q41 q16 perm3 hperm3
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr candidateMapFlow
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP)
    (AspisR1S9CandidateSideOneTailMapV4.candidateAfterOld
      weights ap1 low all first2 q41 q16 perm3)
    (AspisR1S9CandidateSideOneTailMapV4.p6AfterOld
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP ap1)
      (MP low) (MP all) (MP first2)
      (AspisR1S9CandidateHelperV1.toP6Q q41)
      (AspisR1S9CandidateHelperV1.toP6Q q16))
    (fun a => .ok (.cont (iterNext,a)))
    (fun a => .ok (.cont (iterNext,a))) htail
    (by intro a; rfl)

/-- Side zero: the same four term reads and three ordered additions map to the
P6 assembler, then the exact source side-zero tail maps as a Result. -/
theorem candidate_after_terms_side_zero_maps
    (ap1 weights : CA) (iterNext : R) (q41 q8 q12 q16 : CQ)
    (low : C) (perm3 : U) (t0 t1 t2 t3 : C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult candidateMapFlow
      (AspisR1S9CandidateBodyTermsV1.candidateAfterTerms ap1 0#usize iterNext
        weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3) =
    @AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP ap1)
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP
        (AspisR1S9CandidateBodyTermsV1.candidateTerms t0 t1 t2 t3))
      0#usize iterNext (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
      (MP low) (AspisR1S9CandidateHelperV1.toP6Q q41)
      (AspisR1S9CandidateHelperV1.toP6Q q16) := by
  let terms := AspisR1S9CandidateBodyTermsV1.candidateTerms t0 t1 t2 t3
  let pterms := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms
  unfold AspisR1S9CandidateBodyTermsV1.candidateAfterTerms
    AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms
  simp only [if_pos (show (0#usize : U) = 0#usize from rfl), if_true]
  simp_rw [← AspisR1S9CandidateTailFlatBindV1.candidateSideZeroTail_bind,
    ← AspisR1S9CandidateTailFlatBindV1.p6SideZeroTail_bind]
  unfold AspisR1S9HelperP6.field.WideExact.add
  rw [← AspisR1S9CandidateTermSumsFlatBindV2.candidateFourTermSums_bind terms
    (fun sums : C × C × C =>
      (do
        let a ← AspisR1S9CandidateSideZeroTailMapV1.candidateSideZeroTail
          weights low sums.2.1 sums.2.2 q16
        ok (.cont (iterNext,a)) : Result (ControlFlow (R × CA) CA)))]
  rw [← AspisR1S9CandidateTermSumsFlatBindV2.p6FourTermSums_bind pterms
    (fun sums : P × P × P =>
      (do
        let a ← AspisR1.S9SideZeroTailRootV1.sideZeroTail
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
          (MP low) sums.2.1 sums.2.2
          (AspisR1S9CandidateHelperV1.toP6Q q16)
        ok (.cont (iterNext,a)) : Result (ControlFlow (R × PA) PA)))]
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr candidateMapFlow Mout
    (candidateFourTermSums terms) (p6FourTermSums pterms)
    (fun sums => do
      let a ← AspisR1S9CandidateSideZeroTailMapV1.candidateSideZeroTail
        weights low sums.2.1 sums.2.2 q16
      .ok (.cont (iterNext,a)))
    (fun sums => do
      let a ← AspisR1.S9SideZeroTailRootV1.sideZeroTail
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
        (MP low) sums.2.1 sums.2.2 (AspisR1S9CandidateHelperV1.toP6Q q16)
      .ok (.cont (iterNext,a)))
    (AspisR1S9CandidateTermStagesComposeV1.candidate_four_term_sums_maps terms)
    (by intro sums; exact zeroTailFlowMap weights low sums.2.1 sums.2.2 q16 iterNext)

/-- Side one keeps the existing candidate-bound PERM[3] witness and maps the
actual first2/first3/all tuple into the ordered P6 suffix. -/
theorem candidate_after_terms_side_one_maps
    (ap1 weights : CA) (iterNext : R) (q41 q8 q12 q16 : CQ)
    (low : C) (perm3 : U)
    (hperm3 : Array.index_usize
      _root_.AspisR1S9CandidateHelperV1.weights.PERM 3#usize = .ok perm3)
    (t0 t1 t2 t3 : C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult candidateMapFlow
      (AspisR1S9CandidateBodyTermsV1.candidateAfterTerms ap1 1#usize iterNext
        weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3) =
    @AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP ap1)
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP
        (AspisR1S9CandidateBodyTermsV1.candidateTerms t0 t1 t2 t3))
      1#usize iterNext (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
      (MP low) (AspisR1S9CandidateHelperV1.toP6Q q41)
      (AspisR1S9CandidateHelperV1.toP6Q q16) := by
  let terms := AspisR1S9CandidateBodyTermsV1.candidateTerms t0 t1 t2 t3
  let pterms := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms
  unfold AspisR1S9CandidateBodyTermsV1.candidateAfterTerms
    AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms
  have hone : (1#usize : U) ≠ 0#usize := by decide
  simp only [if_neg hone, if_false]
  simp_rw [← AspisR1S9CandidateTailFlatBindV1.candidateAfterOld_bind,
    ← AspisR1S9CandidateTailFlatBindV1.p6AfterOld_bind]
  unfold AspisR1S9HelperP6.field.WideExact.add
  rw [← AspisR1S9CandidateTermSumsFlatBindV2.candidateFourTermSums_bind terms
    (fun sums : C × C × C =>
      (do
        let a ← AspisR1S9CandidateSideOneTailMapV4.candidateAfterOld
          weights ap1 low sums.2.2 sums.1 q41 q16 perm3
        ok (.cont (iterNext,a)) : Result (ControlFlow (R × CA) CA)))]
  rw [← AspisR1S9CandidateTermSumsFlatBindV2.p6FourTermSums_bind pterms
    (fun sums : P × P × P =>
      (do
        let a ← AspisR1S9CandidateSideOneTailMapV4.p6AfterOld
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP ap1)
          (MP low) sums.2.2 sums.1
          (AspisR1S9CandidateHelperV1.toP6Q q41)
          (AspisR1S9CandidateHelperV1.toP6Q q16)
        ok (.cont (iterNext,a)) : Result (ControlFlow (R × PA) PA)))]
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr candidateMapFlow Mout
    (candidateFourTermSums terms) (p6FourTermSums pterms)
    (fun sums => do
      let a ← AspisR1S9CandidateSideOneTailMapV4.candidateAfterOld
        weights ap1 low sums.2.2 sums.1 q41 q16 perm3
      .ok (.cont (iterNext,a)))
    (fun sums => do
      let a ← AspisR1S9CandidateSideOneTailMapV4.p6AfterOld
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP weights)
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP ap1)
        (MP low) sums.2.2 sums.1
        (AspisR1S9CandidateHelperV1.toP6Q q41)
        (AspisR1S9CandidateHelperV1.toP6Q q16)
      .ok (.cont (iterNext,a)))
    (AspisR1S9CandidateTermStagesComposeV1.candidate_four_term_sums_maps terms)
    (by
      intro sums
      exact oneTailFlowMap weights ap1 low sums.2.2 sums.1
        q41 q16 perm3 hperm3 iterNext)

#print axioms AspisR1S9CandidateAfterTermsComposeV1.candidate_after_terms_side_zero_maps
#print axioms AspisR1S9CandidateAfterTermsComposeV1.candidate_after_terms_side_one_maps

end AspisR1S9CandidateAfterTermsComposeV1
