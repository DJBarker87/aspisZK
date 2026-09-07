import AspisFormal.K1.V7Tag73K15SemanticActualLawClosure
import AspisFormal.K1.V7Tag73K15RestrictedMeasureLedger
import AspisFormal.K1.V7Tag73K15RestrictedRelationAlphaActualLawClosure

/-!
# Compiler-clean actual-law closure for Tag-73 K1.5 semantic failures

The final K1.6 theorem requires K1.5 only on its legal same-tape event.  This
module states the semantic source seam at that exact strength and installs it,
together with the already proved relation-alpha bound, into the restricted
eight-category ledger.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K15RestrictedSemanticActualLawClosure

open Module
open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredK15Events
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisK1.V7Tag73K15RestrictedMeasureLedger
open AspisK1.V7Tag73K15RelationAlphaActualLawClosure
open AspisK1.V7Tag73K15RestrictedRelationAlphaActualLawClosure
open AspisK1.V7Tag73K15SemanticActualLawAdapter
open AspisK1.V7Tag73K15SemanticActualLawClosure
open AspisK1.V7Tag73K15SemanticFamilyProbability
open AspisK1.V7Tag73K15SemanticSamplerFactorization
open AspisK1.V7Tag73K15SemanticSamplerFamilyProbability
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73RestoredCausalK15Stage
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Deterministic inclusion of the compiler-clean semantic event in the exact
22-sampler coordinate event. -/
def ExactTag73RestrictedSemanticCover
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {basis : Basis (Fin 4) F QM31Exact}
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    (environment : ExactTag73RestoredCausalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (lanes : ExactTag73SemanticLanes HiddenTape parameters)
    (terminal : ExactTag73SemanticTerminal HiddenTape parameters decoder lanes)
    (sumcheck : ExactTag73SemanticSumcheck HiddenTape parameters decoder lanes) :
    Prop :=
  ∀ hidden, jointEventSlice
      (clean ∩
        (exactTag73RestoredFixedK15Events environment).event .semantic) hidden ⊆
    (exactPlainRomSemanticSamplerCoordinates transitionFuel configuration
      hidden) ⁻¹'
      dependentSuccessfulSubtypeEvent AllSemanticDuplexSamplersSucceed
        (fun residual ↦ successfulSemanticSamplerFamilyCoordinates ⁻¹'
          semanticSkeletonDependentEvent (fun skeleton ↦
            fixedWidth29SemanticValueEvent decoder
              (lanes hidden residual skeleton)
              (terminal hidden residual skeleton)
              (sumcheck hidden residual skeleton)))

/-- Exact actual-law semantic bound on the compiler-clean slice. -/
theorem exact_tag73_restricted_semantic_probability_le_of_source
    {HiddenTape TapeIdentity Observation Payload : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {basis : Basis (Fin 4) F QM31Exact}
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    {environment : ExactTag73RestoredCausalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon}
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (lanes : ExactTag73SemanticLanes HiddenTape parameters)
    (terminal : ExactTag73SemanticTerminal HiddenTape parameters decoder lanes)
    (sumcheck : ExactTag73SemanticSumcheck HiddenTape parameters decoder lanes)
    (covered : ExactTag73RestrictedSemanticCover environment clean lanes
      terminal sumcheck) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩
          (exactTag73RestoredFixedK15Events environment).event .semantic) ≤
      (30500 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  exact exact_compiler_joint_law_semantic_family_probability_le hiddenLaw
    parameters
    (exactPlainRomSemanticSamplerCoordinates transitionFuel configuration)
    decoder lanes terminal sumcheck
    (clean ∩
      (exactTag73RestoredFixedK15Events environment).event .semantic)
    (by exact covered)

/-- Install the clean semantic and relation-alpha sources into the
clean-restricted fixed-family ledger. -/
theorem restricted_fixed_k15_event_bounds_of_semantic_relation_sources
    {HiddenTape TapeIdentity Observation Payload : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {basis : Basis (Fin 4) F QM31Exact}
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    {environment : ExactTag73RestoredCausalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon}
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (remaining : FixedK15EventBoundsExceptSemanticRelationAlpha
      (exactCompilerJointLaw hiddenLaw parameters)
      (restrictFixedK15Events clean
        (exactTag73RestoredFixedK15Events environment)))
    (semanticLanes : ExactTag73SemanticLanes HiddenTape parameters)
    (semanticTerminal : ExactTag73SemanticTerminal HiddenTape parameters decoder
      semanticLanes)
    (semanticSumcheck : ExactTag73SemanticSumcheck HiddenTape parameters decoder
      semanticLanes)
    (semanticCovered : ExactTag73RestrictedSemanticCover environment clean
      semanticLanes semanticTerminal semanticSumcheck)
    (relationSource : ExactTag73RestrictedK15RelationAlphaSource transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon environment clean) :
    FixedK15EventBounds (exactCompilerJointLaw hiddenLaw parameters)
      (restrictFixedK15Events clean
        (exactTag73RestoredFixedK15Events environment)) := by
  refine ⟨fun kind ↦ ?_⟩
  by_cases semantic : kind = .semantic
  · subst kind
    exact (exact_tag73_restricted_semantic_probability_le_of_source hiddenLaw
      clean semanticLanes semanticTerminal semanticSumcheck semanticCovered).trans
        (ordinary_bound_le_common_nonzero_bound 30500)
  · by_cases relation : kind = .relationAlpha
    · subst kind
      exact (exact_tag73_restricted_relation_alpha_probability_le_of_source
        hiddenLaw clean relationSource).trans
          (ordinary_bound_le_common_nonzero_bound 24)
    · exact remaining.category kind semantic relation

#print axioms exact_tag73_restricted_semantic_probability_le_of_source
#print axioms restricted_fixed_k15_event_bounds_of_semantic_relation_sources

end
end AspisK1.V7Tag73K15RestrictedSemanticActualLawClosure
