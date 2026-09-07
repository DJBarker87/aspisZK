import AspisFormal.K1.V7Tag73K15OrdinaryDuplexCoordinates
import AspisFormal.K1.V7Tag73K15SemanticSequentialRouter

/-!
# Exact factorization of all 22 Tag-73 semantic samplers

The deployed semantic router isolates 176 digest answers: four squeeze and
four advance answers for each of 22 ordinary challenges.  This module
reindexes those answers into 22 literal duplex tapes, conditions only on
successful bounded decoding, and factors every successful tape into its full
nuisance skeleton and one exact QM31 value.

No semantic failure event or probability bound is assumed here.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73K15SemanticSamplerFactorization

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73K15OrdinaryDuplexCoordinates
open AspisK1.V7Tag73K15SemanticSequentialRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev SemanticTotalTapeFamily :=
  SemanticOrdinaryPosition → TotalTag73DuplexOrdinaryTape

abbrev SemanticSuccessfulAttemptFamily :=
  SemanticOrdinaryPosition → SuccessfulTag73DuplexOrdinaryAttempt

abbrev SemanticOrdinarySkeletonFamily :=
  SemanticOrdinaryPosition → Tag73CompleteOrdinarySamplerSkeleton

abbrev SemanticOrdinaryValueFamily :=
  SemanticOrdinaryPosition → AspisV5ComponentCQM31TowerExact.QM31Exact

/-- Reindex the router's literal `(position, block, half)` answers into one
four-output/four-advance tape per semantic challenge. -/
def semanticDuplexSlotsEquiv :
    (SemanticDuplexSlot → Digest256) ≃ SemanticTotalTapeFamily where
  toFun tape position :=
    (fun block ↦ tape (position, block, 0),
      fun block ↦ tape (position, block, 1))
  invFun family slot :=
    if slot.2.2 = 0 then family slot.1 |>.1 slot.2.1
    else family slot.1 |>.2 slot.2.1
  left_inv := by
    intro tape
    funext slot
    rcases slot with ⟨position, block, half⟩
    fin_cases half <;> rfl
  right_inv := by
    intro family
    funext position
    apply Prod.ext <;> funext block <;> rfl

/-- Adapter-ready compiler coordinates: residual answers first, followed by
the complete family of 22 literal sampler tapes. -/
def exactPlainRomSemanticSamplerCoordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      FreshAnswerTape Digest256 (semanticRouterResidual parameters) ×
        SemanticTotalTapeFamily :=
  (exactPlainRomSemanticSequentialCoordinates transitionFuel configuration
      hidden).trans
    ((Equiv.prodCongr semanticDuplexSlotsEquiv (Equiv.refl _)).trans
      (Equiv.prodComm _ _))

def AllSemanticDuplexSamplersSucceed
    (family : SemanticTotalTapeFamily) : Prop :=
  ∀ position, Tag73DuplexOrdinarySucceeds (family position)

instance (family : SemanticTotalTapeFamily) :
    Decidable (AllSemanticDuplexSamplersSucceed family) := by
  unfold AllSemanticDuplexSamplersSucceed
  infer_instance

/-- Successful 22-tape families are exactly 22 complete successful ordinary
attempts. -/
def successfulSemanticSamplerFamilyCoordinates :
    {family : SemanticTotalTapeFamily //
      AllSemanticDuplexSamplersSucceed family} ≃
      SemanticSuccessfulAttemptFamily where
  toFun family position :=
    successfulTag73DuplexOrdinaryCoordinates
      ⟨family.1 position, family.2 position⟩
  invFun samples :=
    ⟨fun position ↦
        successfulTag73DuplexOrdinaryCoordinates.symm (samples position),
      fun position ↦
        (successfulTag73DuplexOrdinaryCoordinates.symm
          (samples position)).2⟩
  left_inv := by
    intro family
    apply Subtype.ext
    funext position
    exact congrArg Subtype.val
      (successfulTag73DuplexOrdinaryCoordinates.symm_apply_apply
        ⟨family.1 position, family.2 position⟩)
  right_inv := by
    intro samples
    funext position
    exact successfulTag73DuplexOrdinaryCoordinates.apply_symm_apply
      (samples position)

noncomputable instance :
    Nonempty {family : SemanticTotalTapeFamily //
      AllSemanticDuplexSamplersSucceed family} :=
  Nonempty.map successfulSemanticSamplerFamilyCoordinates.symm inferInstance

/-- Pointwise factorization followed by the canonical separation of all
skeletons from all returned values. -/
def successfulSemanticSamplerFactorization :
    {family : SemanticTotalTapeFamily //
      AllSemanticDuplexSamplersSucceed family} ≃
      SemanticOrdinarySkeletonFamily × SemanticOrdinaryValueFamily :=
  successfulSemanticSamplerFamilyCoordinates.trans
    ((Equiv.piCongrRight fun _ ↦ successfulDuplexOrdinaryFactorization).trans
      { toFun := fun family ↦
          (fun position ↦ (family position).1,
            fun position ↦ (family position).2)
        invFun := fun pair position ↦ (pair.1 position, pair.2 position)
        left_inv := by intro family; rfl
        right_inv := by intro pair; rfl })

@[simp] theorem successfulSemanticSamplerFactorization_value
    (family : {family : SemanticTotalTapeFamily //
      AllSemanticDuplexSamplersSucceed family})
    (position : SemanticOrdinaryPosition) :
    (successfulSemanticSamplerFactorization family).2 position =
      successfulDuplexOrdinaryValue
        (successfulSemanticSamplerFamilyCoordinates family position) := by
  rfl

#print axioms semanticDuplexSlotsEquiv
#print axioms exactPlainRomSemanticSamplerCoordinates
#print axioms successfulSemanticSamplerFamilyCoordinates
#print axioms successfulSemanticSamplerFactorization
#print axioms successfulSemanticSamplerFactorization_value

end

end AspisK1.V7Tag73K15SemanticSamplerFactorization
