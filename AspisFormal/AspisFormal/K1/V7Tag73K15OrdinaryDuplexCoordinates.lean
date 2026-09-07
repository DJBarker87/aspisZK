import AspisFormal.K1.V7Tag73CompleteCausalOrdinaryProbability
import AspisFormal.K1.V7Tag73VariablePrefixGammaFlatRouting

/-!
# Exact total coordinates for one Tag-73 ordinary duplex sampler

The scheduler-native K1.5 routers isolate four squeeze outputs and four
duplex-advance answers.  The probability layer is phrased using a successful
raw ordinary stream paired with the same four advance answers.  This module
gives the exact equivalence between those two representations.

No probability, transcript, source, or acceptance premise occurs here.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K15OrdinaryDuplexCoordinates

open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting

noncomputable section

/-- Literal four-output/four-advance region isolated by an ordinary-challenge
router. -/
abbrev TotalTag73DuplexOrdinaryTape :=
  FourGammaBlocks × Tag73OrdinaryAdvanceDigestGhosts

/-- Success is exactly successful bounded ordinary decoding of the four
squeeze-output blocks.  Advance answers are nuisance data. -/
def Tag73DuplexOrdinarySucceeds
    (tape : TotalTag73DuplexOrdinaryTape) : Prop :=
  Tag73RawSucceeds (fourGammaBlocksRawEquiv tape.1)

instance (tape : TotalTag73DuplexOrdinaryTape) :
    Decidable (Tag73DuplexOrdinarySucceeds tape) := by
  unfold Tag73DuplexOrdinarySucceeds
  infer_instance

/-- Successful literal block tapes are exactly successful complete ordinary
attempts.  Both the rejection-path words and all advance answers are retained
bijectively. -/
def successfulTag73DuplexOrdinaryCoordinates :
    {tape : TotalTag73DuplexOrdinaryTape //
      Tag73DuplexOrdinarySucceeds tape} ≃
      SuccessfulTag73DuplexOrdinaryAttempt where
  toFun tape :=
    (⟨fourGammaBlocksRawEquiv tape.1.1, tape.2⟩, tape.1.2)
  invFun sample :=
    ⟨(fourGammaBlocksRawEquiv.symm sample.1.1, sample.2), by
      simpa [Tag73DuplexOrdinarySucceeds] using sample.1.2⟩
  left_inv := by
    intro tape
    apply Subtype.ext
    apply Prod.ext
    · exact fourGammaBlocksRawEquiv.symm_apply_apply tape.1.1
    · rfl
  right_inv := by
    intro sample
    apply Prod.ext
    · apply Subtype.ext
      exact fourGammaBlocksRawEquiv.apply_symm_apply sample.1.1
    · rfl

noncomputable instance :
    Nonempty {tape : TotalTag73DuplexOrdinaryTape //
      Tag73DuplexOrdinarySucceeds tape} :=
  Nonempty.map successfulTag73DuplexOrdinaryCoordinates.symm inferInstance

@[simp] theorem successfulTag73DuplexOrdinaryCoordinates_value
    (sample : {tape : TotalTag73DuplexOrdinaryTape //
      Tag73DuplexOrdinarySucceeds tape}) :
    successfulDuplexOrdinaryValue
        (successfulTag73DuplexOrdinaryCoordinates sample) =
      tag73FourLimbsToExact
        (successfulTag73Values
          ⟨fourGammaBlocksRawEquiv sample.1.1, sample.2⟩) := by
  rfl

#print axioms Tag73DuplexOrdinarySucceeds
#print axioms successfulTag73DuplexOrdinaryCoordinates
#print axioms successfulTag73DuplexOrdinaryCoordinates_value

end

end AspisK1.V7Tag73K15OrdinaryDuplexCoordinates
