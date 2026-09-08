import AspisFormal.K1.V7Tag73ExactRestoredOperationalK13Events
import AspisFormal.K1.V7Tag73K13RestrictedOneFoldActualLawClosure

/-!
# Restoration-wide canonical-root one-fold probability

This specializes the causal one-fold conditioning theorem to the canonical
accepted root used by the corrected restoration-wide K1.3 classifier.  The
source boundary is deliberately pre-answer: it supplies an exact causal
context for each hidden tape, residual coordinate and successful ordinary
sampler skeleton, plus the deterministic source-event inclusion.  The
degree-three curve argument and compiler-law averaging are proved internally.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredOperationalK13OneFoldProbability

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalK13Events
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

/-- Exact pre-fold-alpha source family for the canonical accepted root on the
compiler-clean slice.  This contains no probability or final bound field. -/
structure ExactTag73RestoredCanonicalOneFoldSource
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
        (clean ∩
          exactTag73RestoredOperationalCanonicalRootK13OneFoldEvent
            transitionFuel configuration projection fixedInstance decoder)
        hidden ⊆
      (exactPlainRomAlphaZeroSamplerCoordinates transitionFuel configuration
          hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent Tag73DuplexOrdinarySucceeds
          (fun residual ↦ successfulTag73DuplexOrdinaryCoordinates ⁻¹'
            duplexOrdinaryDependentEvent
              (causalOneFoldSamplerTarget fun skeleton ↦
                (context hidden residual skeleton).toGeneric))

/-- The canonical-root one-fold failure has the exact raw degree-three bound.
The adaptive response strategy is retained; no post-alpha transcript is frozen
and no proof-of-work normalization is used. -/
theorem exact_restored_operational_canonical_root_k13_onefold_probability_le
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
    (source : ExactTag73RestoredCanonicalOneFoldSource transitionFuel
      configuration projection fixedInstance decoder clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩
          exactTag73RestoredOperationalCanonicalRootK13OneFoldEvent
            transitionFuel configuration projection fixedInstance decoder) ≤
      exactOneFoldIdealRawError := by
  change
    (hiddenTapeUniformFreshJointLaw hiddenLaw
      (exactCompilerTargetCaps parameters).length).toOuterMeasure
        (clean ∩
          exactTag73RestoredOperationalCanonicalRootK13OneFoldEvent
            transitionFuel configuration projection fixedInstance decoder) ≤
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
    (clean ∩
      exactTag73RestoredOperationalCanonicalRootK13OneFoldEvent transitionFuel
        configuration projection fixedInstance decoder)
    source.covered

end

#print axioms ExactTag73RestoredCanonicalOneFoldSource
#print axioms
  exact_restored_operational_canonical_root_k13_onefold_probability_le

end AspisK1.V7Tag73ExactRestoredOperationalK13OneFoldProbability
