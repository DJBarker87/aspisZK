import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events
import AspisFormal.K1.V7Tag73ExactInternalCurveProbability
import AspisFormal.K1.V7Tag73K15RelationAlphaPreAnswerRouters
import AspisFormal.K1.V7Tag73K15OrdinaryDuplexCoordinates
import AspisFormal.K1.V7Tag73SuccessfulOneFoldConditioningBridge
import AspisFormal.K1.V7Tag73K13IdealErrorLedger

/-!
# Compiler-clean actual-law closure for the Tag-73 one-fold event

The fold-alpha coordinates are fixed to the deployed alpha-zero router.  The
source record contains only exact pre-answer algebraic contexts and a
deterministic clean-event inclusion; the V7 degree-three correlated-agreement
theorem is installed internally.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K13RestrictedOneFoldActualLawClosure

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73K15OrdinaryDuplexCoordinates
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73SuccessfulOneFoldConditioningBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Exact pre-fold-alpha source family on one compiler-clean slice. -/
structure ExactTag73RestrictedK13OneFoldSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  context : HiddenTape → FreshAnswerTape Digest256
      (relationAlphaRouterResidual parameters) →
    Tag73CompleteOrdinarySamplerSkeleton → ExactCausalOneFoldSamplerContext
  covered : ∀ hidden,
    jointEventSlice
        (clean ∩ exactTag73K13OneFoldEvent transitionFuel configuration
          projection fixedInstance decoder) hidden ⊆
      (exactPlainRomAlphaZeroSamplerCoordinates transitionFuel configuration
          hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent Tag73DuplexOrdinarySucceeds
          (fun residual ↦ successfulTag73DuplexOrdinaryCoordinates ⁻¹'
            duplexOrdinaryDependentEvent
              (causalOneFoldSamplerTarget fun skeleton ↦
                (context hidden residual skeleton).toGeneric))

/-- Exact compiler-law one-fold bound on the clean slice. -/
theorem exact_tag73_restricted_k13_onefold_probability_le
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (source : ExactTag73RestrictedK13OneFoldSource transitionFuel configuration
      projection fixedInstance decoder clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73K13OneFoldEvent transitionFuel configuration
          projection fixedInstance decoder) ≤ exactOneFoldIdealRawError := by
  change
    (hiddenTapeUniformFreshJointLaw hiddenLaw
      (exactCompilerTargetCaps parameters).length).toOuterMeasure
        (clean ∩ exactTag73K13OneFoldEvent transitionFuel configuration
          projection fixedInstance decoder) ≤
      (AspisV6PublishedTheoremInterfaces.foldChallengeCap : ENNReal) /
        ((P ^ 4 : Nat) : ENNReal)
  exact exact_compiler_dependent_onefold_event_probability_le
    (F := M31Exact) hiddenLaw (exactCompilerTargetCaps parameters).length
    Tag73DuplexOrdinarySucceeds
    (fun hidden ↦ exactPlainRomAlphaZeroSamplerCoordinates transitionFuel
      configuration hidden)
    successfulTag73DuplexOrdinaryCoordinates
    (fun hidden residual skeleton ↦
      (source.context hidden residual skeleton).toGeneric)
    (clean ∩ exactTag73K13OneFoldEvent transitionFuel configuration
      projection fixedInstance decoder)
    source.covered

#print axioms ExactTag73RestrictedK13OneFoldSource
#print axioms exact_tag73_restricted_k13_onefold_probability_le

end
end AspisK1.V7Tag73K13RestrictedOneFoldActualLawClosure
