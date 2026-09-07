import AspisFormal.K1.V7Tag73K15RestrictedMeasureLedger
import AspisFormal.K1.V7Tag73RestoredCausalErrorLedger
import AspisFormal.K1.V7Tag73ProofRelevantUpstreamInterface

/-!
# Compiler-clean composition of restoration-aware Tag-73 K1.5

The K1.6 compiler pays for its causal target event separately.  This module
therefore composes the exact fixed-family and restored-gamma bounds only on the
literal compiler-clean slice consumed by the final capstone.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RestrictedK15EventComposition

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisK1.V7Tag73K15RestrictedMeasureLedger
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73RestoredCausalErrorLedger

noncomputable section

/-- Exact K1.5 composition on a compiler-clean slice.  The numerator and
denominator are identical to the unrestricted ledger; no independence or new
union term is introduced. -/
theorem restricted_restored_k15_error_measure_bound_of_cover
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (fixedEvents : FixedK15Events (ExactCompilerSample HiddenTape parameters))
    (restoredResidual : Set (ExactCompilerSample HiddenTape parameters))
    (covered : k15SpendWitnessErrorEvent stages ⊆
      fixedEvents.failure ∪ restoredResidual)
    (fixedBounds : FixedK15EventBounds
      (exactCompilerJointLaw hiddenLaw parameters)
      (restrictFixedK15Events clean fixedEvents))
    (restoredBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ restoredResidual) ≤ exactK14IdealRawError) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ k15SpendWitnessErrorEvent stages) ≤
      exactK15RestoredCausalRawError := by
  let law := exactCompilerJointLaw hiddenLaw parameters
  have restrictedCover : clean ∩ k15SpendWitnessErrorEvent stages ⊆
      (restrictFixedK15Events clean fixedEvents).failure ∪
        (clean ∩ restoredResidual) := by
    intro sample member
    rcases member with ⟨cleanMember, errorMember⟩
    rcases covered errorMember with fixedMember | residualMember
    · apply Or.inl
      rw [restrict_fixed_k15_failure_eq]
      exact ⟨cleanMember, fixedMember⟩
    · exact Or.inr ⟨cleanMember, residualMember⟩
  calc
    law.toOuterMeasure (clean ∩ k15SpendWitnessErrorEvent stages) ≤
        law.toOuterMeasure
          ((restrictFixedK15Events clean fixedEvents).failure ∪
            (clean ∩ restoredResidual)) :=
      law.toOuterMeasure.mono restrictedCover
    _ ≤ law.toOuterMeasure
          (restrictFixedK15Events clean fixedEvents).failure +
        law.toOuterMeasure (clean ∩ restoredResidual) := measure_union_le _ _
    _ ≤ exactK15IdealRawError + exactK14IdealRawError :=
      add_le_add
        (fixed_k15_failure_probability_le law
          (restrictFixedK15Events clean fixedEvents) fixedBounds)
        restoredBound
    _ = exactK15RestoredCausalRawError := by
      unfold exactK15RestoredCausalRawError
      ac_rfl

end

#print axioms restricted_restored_k15_error_measure_bound_of_cover

end AspisK1.V7Tag73RestrictedK15EventComposition
