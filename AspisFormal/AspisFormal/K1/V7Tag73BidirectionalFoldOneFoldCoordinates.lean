import AspisFormal.K1.V7Tag73BidirectionalFoldAlphaController
import AspisFormal.K1.V7Tag73VariablePrefixGammaFactorization

/-!
# Five-coordinate selected-fold/alpha factorization

This is the probability coordinate system for the bidirectional controller.
It isolates exactly one 31-bit fold-work answer and four alpha-zero raw output
blocks.  Every other compiler answer, including the fold-nonce boundary and
all final/q16 answers, remains in the residual.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldAlphaController
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotMachineRouter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization

noncomputable section

theorem fold_onefold_digest_slot_card :
    Fintype.card FoldOneFoldDigestSlot = 5 := by
  simp [FoldOneFoldDigestSlot]

def foldOneFoldDigestSlotFunctionEquiv :
    (FoldOneFoldDigestSlot → Digest256) ≃
      Digest256 × FourGammaBlocks where
  toFun values := (values none, fun block => values (some block))
  invFun coordinates
    | none => coordinates.1
    | some block => coordinates.2 block
  left_inv values := by
    funext slot
    cases slot <;> rfl
  right_inv coordinates := by
    apply Prod.ext
    · rfl
    · funext block
      rfl

abbrev ExactCompilerBidirectionalFoldOneFoldResidual
    (parameters : ExactCompilerResourceParameters) :=
  FreshAnswerTape Digest256
    ((exactCompilerTargetCaps parameters).length - 5)

abbrev ExactCompilerCausalBidirectionalFoldOneFoldRouter
    (parameters : ExactCompilerResourceParameters) :=
  CausalSlotRouter Digest256 FoldOneFoldDigestSlot Finset.univ
    ((exactCompilerTargetCaps parameters).length - 5)

theorem exact_compiler_tape_has_bidirectional_fold_onefold_capacity
    (parameters : ExactCompilerResourceParameters) :
    5 ≤ (exactCompilerTargetCaps parameters).length := by
  rw [exact_compiler_target_caps_length]
  unfold unifiedFull256ExposureCap full256MachineFreshCap
    sameTapeStartCap deployedFull256VerifierCallCap
  omega

def bidirectionalFoldOneFoldCoordinateRegroup
    (Residual : Type) :
    (Digest256 × FourGammaBlocks) × Residual ≃
      Residual × (Digest256 × FourGammaBlocks) where
  toFun coordinates := (coordinates.2, coordinates.1)
  invFun coordinates := (coordinates.2, coordinates.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact compiler tape as residual × (fold-work × four alpha blocks). -/
def exactCompilerCausalBidirectionalFoldOneFoldCoordinates
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerBidirectionalFoldOneFoldResidual parameters ×
        (Digest256 × FourGammaBlocks) := by
  let total := (exactCompilerTargetCaps parameters).length
  have enough : 5 ≤ total :=
    exact_compiler_tape_has_bidirectional_fold_onefold_capacity parameters
  have totalEq : total = 5 + (total - 5) := by omega
  have slotCard : Fintype.card FoldOneFoldDigestSlot = 5 :=
    fold_onefold_digest_slot_card
  exact
    (Equiv.cast (congrArg (FreshAnswerTape Digest256) totalEq)).trans
      ((castFreshAnswerTape
          (congrArg (fun count => count + (total - 5)) slotCard).symm
        ).trans
        (router.fullCoordinateEquiv.trans
          ((Equiv.prodCongr foldOneFoldDigestSlotFunctionEquiv
            (Equiv.refl (FreshAnswerTape Digest256 (total - 5)))).trans
              (bidirectionalFoldOneFoldCoordinateRegroup
                (FreshAnswerTape Digest256 (total - 5))))))

def bidirectionalFoldAlphaInitialState
    {globalOracleCalls : Nat}
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory :=
  { exposureIndex := 0
    cursor := cursor
    memory := inactiveBidirectionalFoldAlphaMemory }

def exactCompilerBidirectionalFoldOneFoldRouter
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel anchorIndex : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters :=
  ((bidirectionalFoldAlphaController transitionFuel anchorIndex).machine
    transitionFuel).fullRouter
      ((exactCompilerTargetCaps parameters).length - 5)
      (bidirectionalFoldAlphaInitialState cursor)

end

#print axioms foldOneFoldDigestSlotFunctionEquiv
#print axioms exactCompilerCausalBidirectionalFoldOneFoldCoordinates
#print axioms exactCompilerBidirectionalFoldOneFoldRouter

end AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
