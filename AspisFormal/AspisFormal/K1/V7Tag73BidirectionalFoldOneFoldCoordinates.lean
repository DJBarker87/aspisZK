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

/-- The single length cast from the compiler master tape to the five named
fold/alpha slots plus residual tape.  Keeping this cast shared by the source
router and probability equivalence makes their named coordinates
definitionally identical. -/
def bidirectionalFoldNamedSlotTapeEquiv
    (parameters : ExactCompilerResourceParameters) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      FreshAnswerTape Digest256
        ((Finset.univ : Finset FoldOneFoldDigestSlot).card +
          ((exactCompilerTargetCaps parameters).length - 5)) :=
  castFreshAnswerTape (by
    rw [Finset.card_univ, fold_onefold_digest_slot_card]
    exact (Nat.add_sub_of_le
      (exact_compiler_tape_has_bidirectional_fold_onefold_capacity
        parameters)).symm)

def bidirectionalFoldNamedSlotInputTape
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    FreshAnswerTape Digest256
      ((Finset.univ : Finset FoldOneFoldDigestSlot).card +
        ((exactCompilerTargetCaps parameters).length - 5)) :=
  bidirectionalFoldNamedSlotTapeEquiv parameters tape

/-- Exact compiler tape as residual × (fold-work × four alpha blocks). -/
def exactCompilerCausalBidirectionalFoldOneFoldCoordinates
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerBidirectionalFoldOneFoldResidual parameters ×
        (Digest256 × FourGammaBlocks) := by
  exact
    (bidirectionalFoldNamedSlotTapeEquiv parameters).trans
      (router.fullCoordinateEquiv.trans
        ((Equiv.prodCongr foldOneFoldDigestSlotFunctionEquiv
          (Equiv.refl (FreshAnswerTape Digest256
            ((exactCompilerTargetCaps parameters).length - 5)))).trans
            (bidirectionalFoldOneFoldCoordinateRegroup
              (FreshAnswerTape Digest256
                ((exactCompilerTargetCaps parameters).length - 5)))))

/-- The probability equivalence's named component is literally the named
component read by the source router; no second cast or extensional transport
remains between them. -/
@[simp] theorem exactCompilerCausalBidirectionalFoldOneFoldCoordinates_apply
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        tape =
      ((router.fullCoordinateEquiv
          (bidirectionalFoldNamedSlotInputTape parameters tape)).2,
        foldOneFoldDigestSlotFunctionEquiv
          ((router.fullCoordinateEquiv
            (bidirectionalFoldNamedSlotInputTape parameters tape)).1)) := by
  rfl

/-- The fold component of the public product is the underlying router's
`none` named slot. -/
theorem bidirectional_fold_coordinate_eq_named_slot
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
      tape).2.1 =
        (router.coordinateEquiv
          (bidirectionalFoldNamedSlotInputTape parameters tape)).1
            ⟨none, Finset.mem_univ none⟩ := by
  simp only [exactCompilerCausalBidirectionalFoldOneFoldCoordinates,
    bidirectionalFoldNamedSlotTapeEquiv,
    bidirectionalFoldNamedSlotInputTape,
    CausalSlotRouter.fullCoordinateEquiv, Equiv.trans_apply,
    Equiv.prodCongr_apply, foldOneFoldDigestSlotFunctionEquiv,
    bidirectionalFoldOneFoldCoordinateRegroup, univSubtypeEquiv]
  rfl

/-- Each alpha component of the public product is the underlying router's
corresponding `some block` named slot. -/
theorem bidirectional_alpha_coordinate_eq_named_slot
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (block : Fin 4) :
    (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
      tape).2.2 block =
        (router.coordinateEquiv
          (bidirectionalFoldNamedSlotInputTape parameters tape)).1
            ⟨some block, Finset.mem_univ (some block)⟩ := by
  simp only [exactCompilerCausalBidirectionalFoldOneFoldCoordinates,
    bidirectionalFoldNamedSlotTapeEquiv,
    bidirectionalFoldNamedSlotInputTape,
    CausalSlotRouter.fullCoordinateEquiv, Equiv.trans_apply,
    Equiv.prodCongr_apply, foldOneFoldDigestSlotFunctionEquiv,
    bidirectionalFoldOneFoldCoordinateRegroup, univSubtypeEquiv]
  rfl

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
#print axioms bidirectionalFoldNamedSlotTapeEquiv
#print axioms exactCompilerCausalBidirectionalFoldOneFoldCoordinates
#print axioms exactCompilerCausalBidirectionalFoldOneFoldCoordinates_apply
#print axioms bidirectional_fold_coordinate_eq_named_slot
#print axioms bidirectional_alpha_coordinate_eq_named_slot
#print axioms exactCompilerBidirectionalFoldOneFoldRouter

end AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
