import AspisFormal.K1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
import AspisFormal.K1.V7Tag73CausalGammaPrefixCoordinates

/-!
# Exact 542-slot compiler coordinates through query batching

The corrected K1.3 actual-law argument must freeze every causally earlier
answer before treating the nonzero query-batch challenge as the remaining
random coordinate.  The established profile already names fold work, the
four alpha-zero blocks, final work, and the complete q16 forest (518 answers).
This module adds the twelve query-batch squeeze outputs and their twelve
paired transcript advances.

This is only a lossless coordinate equivalence.  It changes neither the
protocol nor its random-oracle budget.  The source controller that realizes
these slots on the adversary-first scheduler is supplied separately.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler

noncomputable section

/-- The 518 established K1.3 coordinates followed by all 24 coordinates of
the bounded nonzero query-batch duplex. -/
abbrev FoldAlphaFinalWorkQ16QueryBatchDigestSlot :=
  FoldAlphaFinalWorkQ16DigestSlot ⊕ GammaPrefixDigestSlot

theorem fold_alpha_final_work_q16_query_batch_digest_slot_card :
    Fintype.card FoldAlphaFinalWorkQ16QueryBatchDigestSlot = 542 := by
  simp [FoldAlphaFinalWorkQ16QueryBatchDigestSlot,
    FoldAlphaFinalWorkQ16DigestSlot, GammaPrefixDigestSlot]

/-- Split the named-slot function into the already-proved 518-coordinate
profile and the exact bounded query-batch duplex tape. -/
def foldAlphaFinalWorkQ16QueryBatchDigestSlotFunctionEquiv :
    (FoldAlphaFinalWorkQ16QueryBatchDigestSlot → Digest256) ≃
      (Digest256 ×
        (AlphaZeroDigestBlocks ×
          (Digest256 × Q16CandidateDigestForest))) ×
        TotalGammaDuplexTape :=
  (Equiv.sumArrowEquivProdArrow FoldAlphaFinalWorkQ16DigestSlot
      GammaPrefixDigestSlot Digest256).trans
    (Equiv.prodCongr foldAlphaFinalWorkQ16DigestSlotFunctionEquiv
      gammaPrefixDigestSlotFunctionEquiv)

abbrev ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual
    (parameters : ExactCompilerResourceParameters) :=
  FreshAnswerTape Digest256
    ((exactCompilerTargetCaps parameters).length - 542)

abbrev ExactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchRouter
    (parameters : ExactCompilerResourceParameters) :=
  CausalSlotRouter Digest256 FoldAlphaFinalWorkQ16QueryBatchDigestSlot
    Finset.univ ((exactCompilerTargetCaps parameters).length - 542)

theorem exact_compiler_tape_has_fold_alpha_final_work_q16_query_batch_capacity
    (parameters : ExactCompilerResourceParameters) :
    542 ≤ (exactCompilerTargetCaps parameters).length := by
  rw [exact_compiler_target_caps_length]
  unfold unifiedFull256ExposureCap full256MachineFreshCap
    sameTapeStartCap deployedFull256VerifierCallCap
  omega

/-- Put all causally earlier K1.3 coordinates in the left context and retain
the complete query-batch duplex as the final factor. -/
def foldAlphaFinalWorkQ16QueryBatchCoordinateRegroup
    (Residual : Type) :
    ((Digest256 ×
        (AlphaZeroDigestBlocks ×
          (Digest256 × Q16CandidateDigestForest))) ×
        TotalGammaDuplexTape) × Residual ≃
      (Residual ×
        (Digest256 ×
          (AlphaZeroDigestBlocks ×
            (Digest256 × Q16CandidateDigestForest)))) ×
        TotalGammaDuplexTape where
  toFun coordinates :=
    ((coordinates.2, coordinates.1.1), coordinates.1.2)
  invFun coordinates :=
    ((coordinates.1.2, coordinates.2), coordinates.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The literal compiler answer tape is exactly the complete pre-query-batch
context times the bounded query-batch duplex. -/
def exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchRouter
      parameters) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
        (Digest256 ×
          (AlphaZeroDigestBlocks ×
            (Digest256 × Q16CandidateDigestForest)))) ×
        TotalGammaDuplexTape := by
  let total := (exactCompilerTargetCaps parameters).length
  have enough : 542 ≤ total :=
    exact_compiler_tape_has_fold_alpha_final_work_q16_query_batch_capacity
      parameters
  have totalEq : total = 542 + (total - 542) := by omega
  have slotCard :
      Fintype.card FoldAlphaFinalWorkQ16QueryBatchDigestSlot = 542 :=
    fold_alpha_final_work_q16_query_batch_digest_slot_card
  exact
    (Equiv.cast (congrArg (FreshAnswerTape Digest256) totalEq)).trans
      ((castFreshAnswerTape
          (congrArg (fun count ↦ count + (total - 542)) slotCard).symm
        ).trans
        (router.fullCoordinateEquiv.trans
          ((Equiv.prodCongr
              foldAlphaFinalWorkQ16QueryBatchDigestSlotFunctionEquiv
              (Equiv.refl (FreshAnswerTape Digest256 (total - 542)))).trans
            (foldAlphaFinalWorkQ16QueryBatchCoordinateRegroup
              (FreshAnswerTape Digest256 (total - 542))))))

#print axioms fold_alpha_final_work_q16_query_batch_digest_slot_card
#print axioms foldAlphaFinalWorkQ16QueryBatchDigestSlotFunctionEquiv
#print axioms
  exact_compiler_tape_has_fold_alpha_final_work_q16_query_batch_capacity
#print axioms foldAlphaFinalWorkQ16QueryBatchCoordinateRegroup
#print axioms
  exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates

end
end AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
