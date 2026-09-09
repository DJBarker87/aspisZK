import AspisFormal.K1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
import AspisFormal.K1.V7Tag73AdaptiveFoldFinalWorkQ16TrialAccounting
import AspisFormal.K1.V7Tag73CandidateDirectedQueryBatchAccounting
import AspisFormal.K1.V7Tag73K15FixedActualLawAdapters

/-!
# Fold/final-work qualified query-batch probability

The candidate-directed query-batch router names the complete 542-coordinate
profile: fold work, alpha zero, final work, q16, and the bounded query-batch
duplex.  This file proves the probability theorem appropriate to that
chronology.  Alpha and q16 are arbitrary conditioning data.  The two work
digests contribute their literal 31- and 34-bit factors, while the final
nonzero query-batch challenge contributes only its finite target cardinality.

No transcript role, independence premise, or cryptographic assumption is
introduced here; this is exact finite probability accounting.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73CausalFoldFinalWorkQueryBatchProbability

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveFoldFinalWorkQ16TrialAccounting
open AspisK1.V7Tag73CandidateDirectedQueryBatchAccounting
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K15FixedActualLawAdapters
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFlatProbability
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisV5ComponentCQM31TowerExact

noncomputable section

local instance finalWork34AcceptedDecidable (work : Digest256) :
    Decidable (FinalWork34Accepted work) := Classical.propDecidable _

/-- One complete bounded query-batch duplex hits a nuisance-dependent finite
set of nonzero QM31 challenges. -/
theorem uniform_total_gamma_skeleton_target_probability_le
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    (PMF.uniformOfFintype TotalGammaDuplexTape).toOuterMeasure
        (successfulSubtypeEvent GammaPrefixSucceeds
          (successfulGammaPrefixSkeletonDependentEvent target)) ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  exact (uniform_successful_subtype_event_probability_le GammaPrefixSucceeds
      (successfulGammaPrefixSkeletonDependentEvent target)).trans
    (successful_gamma_prefix_skeleton_dependent_probability_le target cap
      targetCap)

/-- Final-work acceptance paired with a later successful query-batch target.
The target may depend on the already exposed final-work answer. -/
def finalWorkQueryBatchDependentEvent
    (target : Digest256 → VariableGammaCompleteSkeleton →
      Finset QM31Exact) :
    Set (Digest256 × TotalGammaDuplexTape) :=
  {coordinates |
    FinalWork34Accepted coordinates.1 ∧
      coordinates.2 ∈
        successfulSubtypeEvent GammaPrefixSucceeds
          (successfulGammaPrefixSkeletonDependentEvent
            (target coordinates.1))}

theorem product_slice_final_work_query_batch
    (target : Digest256 → VariableGammaCompleteSkeleton →
      Finset QM31Exact)
    (work : Digest256) :
    productEventFstSlice (finalWorkQueryBatchDependentEvent target) work =
      if FinalWork34Accepted work then
        successfulSubtypeEvent GammaPrefixSucceeds
          (successfulGammaPrefixSkeletonDependentEvent (target work))
      else ∅ := by
  ext tape
  by_cases accepted : FinalWork34Accepted work <;>
    simp [productEventFstSlice, finalWorkQueryBatchDependentEvent, accepted]

/-- The final-work qualified query-batch event has the exact product of the
34-bit work factor and the nonzero-field target bound. -/
theorem uniform_final_work_query_batch_probability_le
    (target : Digest256 → VariableGammaCompleteSkeleton →
      Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ work skeleton, (target work skeleton).card ≤ cap) :
    (PMF.uniformOfFintype
      (Digest256 × TotalGammaDuplexTape)).toOuterMeasure
        (finalWorkQueryBatchDependentEvent target) ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) := by
  let bound : ENNReal :=
    (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)
  rw [uniform_product_event_probability_eq_weighted_slices]
  calc
    (∑' work : Digest256,
        (PMF.uniformOfFintype Digest256) work *
          (PMF.uniformOfFintype TotalGammaDuplexTape).toOuterMeasure
            (productEventFstSlice
              (finalWorkQueryBatchDependentEvent target) work)) ≤
      ∑' work : Digest256,
        (PMF.uniformOfFintype Digest256) work *
          (if FinalWork34Accepted work then bound else 0) := by
      exact ENNReal.tsum_le_tsum fun work ↦ by
        apply mul_le_mul_left'
        rw [product_slice_final_work_query_batch]
        by_cases accepted : FinalWork34Accepted work
        · simp only [accepted, if_true]
          exact uniform_total_gamma_skeleton_target_probability_le
            (target work) cap (targetCap work)
        · simp [accepted]
    _ = (∑' work : Digest256,
          finalWork34AcceptedEvent.indicator
            (fun work ↦ (PMF.uniformOfFintype Digest256) work) work) *
        bound := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro work
      by_cases accepted : FinalWork34Accepted work <;>
        simp [finalWork34AcceptedEvent, accepted]
    _ = (PMF.uniformOfFintype Digest256).toOuterMeasure
          finalWork34AcceptedEvent * bound := by
      rw [PMF.toOuterMeasure_apply]
    _ = ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) := by
      rw [uniform_final_work_34_probability_exact]

/-- Fold-work acceptance paired with the final-work/query-batch event.  The
finite target may depend on both earlier work answers. -/
def foldFinalWorkQueryBatchDependentEvent
    (target : Digest256 → Digest256 →
      VariableGammaCompleteSkeleton → Finset QM31Exact) :
    Set (Digest256 × (Digest256 × TotalGammaDuplexTape)) :=
  {coordinates |
    FoldWork31Accepted coordinates.1 ∧
      coordinates.2 ∈
        finalWorkQueryBatchDependentEvent (target coordinates.1)}

theorem product_slice_fold_final_work_query_batch
    (target : Digest256 → Digest256 →
      VariableGammaCompleteSkeleton → Finset QM31Exact)
    (fold : Digest256) :
    productEventFstSlice
        (foldFinalWorkQueryBatchDependentEvent target) fold =
      if FoldWork31Accepted fold then
        finalWorkQueryBatchDependentEvent (target fold)
      else ∅ := by
  classical
  ext coordinates
  by_cases accepted : FoldWork31Accepted fold <;>
    simp [productEventFstSlice, foldFinalWorkQueryBatchDependentEvent,
      accepted]

/-- The exact per-trial product bound.  It is deliberately stated before any
finite union over source exposure trials. -/
theorem uniform_fold_final_work_query_batch_probability_le
    (target : Digest256 → Digest256 →
      VariableGammaCompleteSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ fold work skeleton,
      (target fold work skeleton).card ≤ cap) :
    (PMF.uniformOfFintype
      (Digest256 × (Digest256 × TotalGammaDuplexTape))).toOuterMeasure
        (foldFinalWorkQueryBatchDependentEvent target) ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal))) := by
  let bound : ENNReal :=
    ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
      ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal))
  rw [uniform_product_event_probability_eq_weighted_slices]
  calc
    (∑' fold : Digest256,
        (PMF.uniformOfFintype Digest256) fold *
          (PMF.uniformOfFintype
            (Digest256 × TotalGammaDuplexTape)).toOuterMeasure
              (productEventFstSlice
                (foldFinalWorkQueryBatchDependentEvent target) fold)) ≤
      ∑' fold : Digest256,
        (PMF.uniformOfFintype Digest256) fold *
          (if FoldWork31Accepted fold then bound else 0) := by
      exact ENNReal.tsum_le_tsum fun fold ↦ by
        apply mul_le_mul_left'
        rw [product_slice_fold_final_work_query_batch]
        by_cases accepted : FoldWork31Accepted fold
        · simp only [accepted, if_true]
          exact uniform_final_work_query_batch_probability_le
            (target fold) cap (targetCap fold)
        · simp [accepted]
    _ = (∑' fold : Digest256,
          foldWork31AcceptedEvent.indicator
            (fun fold ↦ (PMF.uniformOfFintype Digest256) fold) fold) *
        bound := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro fold
      by_cases accepted : FoldWork31Accepted fold <;>
        simp [foldWork31AcceptedEvent, accepted]
    _ = (PMF.uniformOfFintype Digest256).toOuterMeasure
          foldWork31AcceptedEvent * bound := by
      rw [PMF.toOuterMeasure_apply]
    _ = ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal))) := by
      rw [uniform_fold_work_31_probability_exact]

/-- Reassociate the exact 542-slot coordinate output so alpha and q16 remain
in the nuisance context while fold work, final work, and query batch form the
probability-bearing suffix. -/
def foldFinalWorkQueryBatchCoordinateRegroup
    (Residual Alpha Q16 : Type) :
    ((Residual ×
        (Digest256 × (Alpha × (Digest256 × Q16)))) ×
      TotalGammaDuplexTape) ≃
      (Residual × (Alpha × Q16)) ×
        (Digest256 × (Digest256 × TotalGammaDuplexTape)) where
  toFun coordinates :=
    ((coordinates.1.1, (coordinates.1.2.2.1,
      coordinates.1.2.2.2.2)),
      (coordinates.1.2.1, (coordinates.1.2.2.2.1, coordinates.2)))
  invFun coordinates :=
    ((coordinates.1.1,
      (coordinates.2.1,
        (coordinates.1.2.1, (coordinates.2.2.1, coordinates.1.2.2)))),
      coordinates.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transport the exact product theorem through an arbitrary 542-slot causal
coordinate equivalence. -/
theorem uniform_tape_dependent_fold_final_work_query_batch_probability_le
    {Tape Context : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Context] [Nonempty Context]
    (coordinates : Tape ≃
      Context × (Digest256 × (Digest256 × TotalGammaDuplexTape)))
    (target : Context → Digest256 → Digest256 →
      VariableGammaCompleteSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ context fold work skeleton,
      (target context fold work skeleton).card ≤ cap)
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹' {
      coordinates | coordinates.2 ∈
        foldFinalWorkQueryBatchDependentEvent (target coordinates.1) }) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal))) := by
  let bad : Set
      (Context × (Digest256 × (Digest256 × TotalGammaDuplexTape))) :=
    {coordinates | coordinates.2 ∈
      foldFinalWorkQueryBatchDependentEvent (target coordinates.1)}
  calc
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
        (PMF.uniformOfFintype Tape).toOuterMeasure (coordinates ⁻¹' bad) :=
      (PMF.uniformOfFintype Tape).toOuterMeasure.mono covered
    _ = ((PMF.uniformOfFintype Tape).map coordinates).toOuterMeasure bad := by
      rw [PMF.toOuterMeasure_map_apply]
    _ = (PMF.uniformOfFintype
          (Context ×
            (Digest256 × (Digest256 × TotalGammaDuplexTape)))).toOuterMeasure
          bad := by
      rw [AspisV5RankOneOpeningHiding.uniform_map_equiv coordinates]
    _ ≤ _ := by
      rw [uniform_product_event_probability_eq_weighted_slices]
      calc
        (∑' context : Context,
          (PMF.uniformOfFintype Context) context *
            (PMF.uniformOfFintype
              (Digest256 ×
                (Digest256 × TotalGammaDuplexTape))).toOuterMeasure
              (productEventFstSlice bad context)) ≤
          ∑' context : Context,
            (PMF.uniformOfFintype Context) context *
              (((1 : ENNReal) / (2 : ENNReal) ^ 31) *
                (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
                  ((cap : ENNReal) /
                    ((P ^ 4 - 1 : Nat) : ENNReal)))) := by
          exact ENNReal.tsum_le_tsum fun context ↦ by
            apply mul_le_mul_left'
            have sliceExact : productEventFstSlice bad context =
                foldFinalWorkQueryBatchDependentEvent (target context) := by
              rfl
            rw [sliceExact]
            exact uniform_fold_final_work_query_batch_probability_le
              (target context) cap (targetCap context)
        _ = (∑' context : Context,
              (PMF.uniformOfFintype Context) context) *
              (((1 : ENNReal) / (2 : ENNReal) ^ 31) *
                (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
                  ((cap : ENNReal) /
                    ((P ^ 4 - 1 : Nat) : ENNReal)))) := by
          rw [ENNReal.tsum_mul_right]
        _ = _ := by rw [PMF.tsum_coe, one_mul]

/-- Hidden-tape averaged form for any exact 542-slot causal router. -/
theorem exact_compiler_causal_fold_final_work_query_batch_probability_le
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (router : HiddenTape →
      ExactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchRouter parameters)
    (target : HiddenTape →
      (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
        (AlphaZeroDigestBlocks × Q16CandidateDigestForest)) →
      Digest256 → Digest256 → VariableGammaCompleteSkeleton →
        Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ hidden context fold work skeleton,
      (target hidden context fold work skeleton).card ≤ cap)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      ((exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
        parameters (router hidden)).trans
          (foldFinalWorkQueryBatchCoordinateRegroup
            (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters)
            AlphaZeroDigestBlocks Q16CandidateDigestForest)) ⁻¹' {
        coordinates | coordinates.2 ∈
          foldFinalWorkQueryBatchDependentEvent
            (target hidden coordinates.1) }) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal))) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_fold_final_work_query_batch_probability_le
    ((exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
      (router hidden)).trans
        (foldFinalWorkQueryBatchCoordinateRegroup
          (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters)
          AlphaZeroDigestBlocks Q16CandidateDigestForest))
    (target hidden) cap (targetCap hidden) (jointEventSlice event hidden)
    (covered hidden)

/-! ## Exact work-trial and candidate accounting -/

/-- Probability-ready family for the deployed source bridge.  Fold and final
exposure trials remain separate so their finite unions cancel against the
literal 31- and 34-bit work factors.  Only the pre-fixed q16 terminal-slot
hypothesis survives as the conservative factor of 512. -/
structure ExactCompilerCandidateDirectedQueryBatchTrials
    {HiddenTape FoldTrial FinalTrial : Type}
    [Fintype HiddenTape] [Fintype FoldTrial] [Fintype FinalTrial]
    (parameters : ExactCompilerResourceParameters) where
  event : Q16DigestSlot → FoldTrial → FinalTrial →
    Set (ExactCompilerSample HiddenTape parameters)
  router : Q16DigestSlot → FoldTrial → FinalTrial → HiddenTape →
    ExactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchRouter parameters
  target : Q16DigestSlot → FoldTrial → FinalTrial → HiddenTape →
    (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)) →
    Digest256 → Digest256 → VariableGammaCompleteSkeleton →
      Finset QM31Exact
  targetCard : ∀ candidate foldTrial finalTrial hidden context fold work
      skeleton,
    (target candidate foldTrial finalTrial hidden context fold work
      skeleton).card ≤ 16
  covered : ∀ candidate foldTrial finalTrial hidden,
    jointEventSlice (event candidate foldTrial finalTrial) hidden ⊆
      ((exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
        parameters (router candidate foldTrial finalTrial hidden)).trans
          (foldFinalWorkQueryBatchCoordinateRegroup
            (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters)
            AlphaZeroDigestBlocks Q16CandidateDigestForest)) ⁻¹' {
        coordinates | coordinates.2 ∈
          foldFinalWorkQueryBatchDependentEvent
            (target candidate foldTrial finalTrial hidden coordinates.1) }

def ExactCompilerCandidateDirectedQueryBatchTrials.failureUnion
    {HiddenTape FoldTrial FinalTrial : Type}
    [Fintype HiddenTape] [Fintype FoldTrial] [Fintype FinalTrial]
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCandidateDirectedQueryBatchTrials
      (HiddenTape := HiddenTape) (FoldTrial := FoldTrial)
      (FinalTrial := FinalTrial) parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  ⋃ candidate, ⋃ foldTrial, ⋃ finalTrial,
    trials.event candidate foldTrial finalTrial

theorem ExactCompilerCandidateDirectedQueryBatchTrials.event_probability_le
    {HiddenTape FoldTrial FinalTrial : Type}
    [Fintype HiddenTape] [Fintype FoldTrial] [Fintype FinalTrial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCandidateDirectedQueryBatchTrials
      (HiddenTape := HiddenTape) (FoldTrial := FoldTrial)
      (FinalTrial := FinalTrial) parameters)
    (candidate : Q16DigestSlot) (foldTrial : FoldTrial)
    (finalTrial : FinalTrial) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event candidate foldTrial finalTrial) ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          ((16 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal))) := by
  exact exact_compiler_causal_fold_final_work_query_batch_probability_le
    hiddenLaw parameters (trials.router candidate foldTrial finalTrial)
    (trials.target candidate foldTrial finalTrial) 16
    (trials.targetCard candidate foldTrial finalTrial)
    (trials.event candidate foldTrial finalTrial)
    (trials.covered candidate foldTrial finalTrial)

/-- After exact cancellation of both work-qualified trial inventories, one
pre-fixed q16 candidate costs only the degree-sixteen field term. -/
theorem ExactCompilerCandidateDirectedQueryBatchTrials.candidate_probability_le
    {HiddenTape FoldTrial FinalTrial : Type}
    [Fintype HiddenTape] [Fintype FoldTrial] [Fintype FinalTrial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCandidateDirectedQueryBatchTrials
      (HiddenTape := HiddenTape) (FoldTrial := FoldTrial)
      (FinalTrial := FinalTrial) parameters)
    (foldTrialCap : Fintype.card FoldTrial ≤ 2 ^ 31)
    (finalTrialCap : Fintype.card FinalTrial ≤ 2 ^ 34)
    (candidate : Q16DigestSlot) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ foldTrial, ⋃ finalTrial,
          trials.event candidate foldTrial finalTrial) ≤
      (16 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  let law := exactCompilerJointLaw hiddenLaw parameters
  let base : ENNReal :=
    (16 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)
  have finalBound (foldTrial : FoldTrial) :
      law.toOuterMeasure
          (⋃ finalTrial, trials.event candidate foldTrial finalTrial) ≤
        ((1 : ENNReal) / (2 : ENNReal) ^ 31) * base := by
    apply finite_work_trial_union_probability_le_base law 34
      (((1 : ENNReal) / (2 : ENNReal) ^ 31) * base)
      (fun finalTrial ↦ trials.event candidate foldTrial finalTrial)
    · intro finalTrial
      have bound := trials.event_probability_le
        (hiddenLaw := hiddenLaw) candidate foldTrial finalTrial
      calc
        law.toOuterMeasure (trials.event candidate foldTrial finalTrial) ≤
            ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
              (((1 : ENNReal) / (2 : ENNReal) ^ 34) * base) := by
          simpa [law, base] using bound
        _ = (((1 : ENNReal) / (2 : ENNReal) ^ 31) * base) /
            (2 : ENNReal) ^ 34 := by
          simp only [div_eq_mul_inv]
          ring
    · exact finalTrialCap
  apply finite_work_trial_union_probability_le_base law 31 base
    (fun foldTrial ↦ ⋃ finalTrial,
      trials.event candidate foldTrial finalTrial)
  · intro foldTrial
    calc
      law.toOuterMeasure
          (⋃ finalTrial, trials.event candidate foldTrial finalTrial) ≤
          ((1 : ENNReal) / (2 : ENNReal) ^ 31) * base :=
        finalBound foldTrial
      _ = base / (2 : ENNReal) ^ 31 := by
        simp only [div_eq_mul_inv]
        ring
  · exact foldTrialCap

/-- Complete 512-candidate actual-law accounting.  Work-trial multiplicities
cancel exactly; the only remaining union factor is the finite q16 terminal
slot cover. -/
theorem ExactCompilerCandidateDirectedQueryBatchTrials.failure_probability_le
    {HiddenTape FoldTrial FinalTrial : Type}
    [Fintype HiddenTape] [Fintype FoldTrial] [Fintype FinalTrial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCandidateDirectedQueryBatchTrials
      (HiddenTape := HiddenTape) (FoldTrial := FoldTrial)
      (FinalTrial := FinalTrial) parameters)
    (foldTrialCap : Fintype.card FoldTrial ≤ 2 ^ 31)
    (finalTrialCap : Fintype.card FinalTrial ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        trials.failureUnion ≤ candidateDirectedJointBatchRawError := by
  have bound := candidate_directed_joint_batch_union_probability_le
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
    (fun candidate ↦ ⋃ foldTrial, ⋃ finalTrial,
      trials.event candidate foldTrial finalTrial)
    (fun candidate ↦
      trials.candidate_probability_le foldTrialCap finalTrialCap candidate)
  simpa [ExactCompilerCandidateDirectedQueryBatchTrials.failureUnion] using
    bound

#print axioms uniform_total_gamma_skeleton_target_probability_le
#print axioms product_slice_final_work_query_batch
#print axioms uniform_final_work_query_batch_probability_le
#print axioms product_slice_fold_final_work_query_batch
#print axioms uniform_fold_final_work_query_batch_probability_le
#print axioms foldFinalWorkQueryBatchCoordinateRegroup
#print axioms
  uniform_tape_dependent_fold_final_work_query_batch_probability_le
#print axioms
  exact_compiler_causal_fold_final_work_query_batch_probability_le
#print axioms ExactCompilerCandidateDirectedQueryBatchTrials
#print axioms ExactCompilerCandidateDirectedQueryBatchTrials.event_probability_le
#print axioms
  ExactCompilerCandidateDirectedQueryBatchTrials.candidate_probability_le
#print axioms
  ExactCompilerCandidateDirectedQueryBatchTrials.failure_probability_le

end
end AspisK1.V7Tag73CausalFoldFinalWorkQueryBatchProbability
