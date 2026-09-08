import AspisFormal.K1.V7Tag73K15RestrictedSemanticActualLawClosure
import AspisFormal.K1.V7Tag73PreQ16K15RestrictedRelationAlphaActualLawClosure

/-!
# Actual-law semantic closure for corrected pre-q16 K1.5

The semantic sampler-family argument is unchanged, but its literal failure
event is indexed by the corrected chronological K1.3 words and coherent K1.4
extraction.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16K15RestrictedSemanticActualLawClosure

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
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisK1.V7Tag73K15RestrictedMeasureLedger
open AspisK1.V7Tag73K15SemanticActualLawAdapter
open AspisK1.V7Tag73K15SemanticActualLawClosure
open AspisK1.V7Tag73K15SemanticFamilyProbability
open AspisK1.V7Tag73K15SemanticSamplerFactorization
open AspisK1.V7Tag73K15SemanticSamplerFamilyProbability
open AspisK1.V7Tag73PreQ16K15RestrictedRelationAlphaActualLawClosure
open AspisK1.V7Tag73PreQ16RestoredK15Context
open AspisK1.V7Tag73PreQ16RestoredK15Events
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Deterministic inclusion of the corrected semantic event in the exact
22-sampler coordinate event. -/
def ExactTag73RestrictedPreQ16SemanticCover
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
    {basis : Basis (Fin 4) F QM31Exact} {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    (environment : ExactPreQ16RestoredK15Environment transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (lanes : ExactTag73SemanticLanes HiddenTape parameters)
    (terminal : ExactTag73SemanticTerminal HiddenTape parameters decoder lanes)
    (sumcheck : ExactTag73SemanticSumcheck HiddenTape parameters decoder lanes) :
    Prop :=
  ∀ hidden, jointEventSlice
      (clean ∩
        (exactPreQ16RestoredFixedK15Events environment).event .semantic) hidden ⊆
    (exactPlainRomSemanticSamplerCoordinates transitionFuel configuration
      hidden) ⁻¹'
      dependentSuccessfulSubtypeEvent AllSemanticDuplexSamplersSucceed
        (fun residual ↦ successfulSemanticSamplerFamilyCoordinates ⁻¹'
          semanticSkeletonDependentEvent (fun skeleton ↦
            fixedWidth29SemanticValueEvent decoder
              (lanes hidden residual skeleton)
              (terminal hidden residual skeleton)
              (sumcheck hidden residual skeleton)))

theorem exact_tag73_restricted_preQ16_semantic_probability_le_of_source
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
    {basis : Basis (Fin 4) F QM31Exact} {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    {environment : ExactPreQ16RestoredK15Environment transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon}
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (lanes : ExactTag73SemanticLanes HiddenTape parameters)
    (terminal : ExactTag73SemanticTerminal HiddenTape parameters decoder lanes)
    (sumcheck : ExactTag73SemanticSumcheck HiddenTape parameters decoder lanes)
    (covered : ExactTag73RestrictedPreQ16SemanticCover environment clean lanes
      terminal sumcheck) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩
          (exactPreQ16RestoredFixedK15Events environment).event .semantic) ≤
      (30500 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  exact exact_compiler_joint_law_semantic_family_probability_le hiddenLaw
    parameters
    (exactPlainRomSemanticSamplerCoordinates transitionFuel configuration)
    decoder lanes terminal sumcheck
    (clean ∩
      (exactPreQ16RestoredFixedK15Events environment).event .semantic)
    covered

/-- Install the corrected semantic and relation-alpha source theorems.  The
remaining record contains only the other six fixed categories. -/
theorem restricted_preQ16_fixed_k15_event_bounds_of_semantic_relation_sources
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
    {basis : Basis (Fin 4) F QM31Exact} {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    {environment : ExactPreQ16RestoredK15Environment transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon}
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (remaining : FixedK15EventBoundsExceptSemanticRelationAlpha
      (exactCompilerJointLaw hiddenLaw parameters)
      (restrictFixedK15Events clean
        (exactPreQ16RestoredFixedK15Events environment)))
    (semanticLanes : ExactTag73SemanticLanes HiddenTape parameters)
    (semanticTerminal : ExactTag73SemanticTerminal HiddenTape parameters decoder
      semanticLanes)
    (semanticSumcheck : ExactTag73SemanticSumcheck HiddenTape parameters decoder
      semanticLanes)
    (semanticCovered : ExactTag73RestrictedPreQ16SemanticCover environment clean
      semanticLanes semanticTerminal semanticSumcheck)
    (relationSource : ExactTag73RestrictedPreQ16K15RelationAlphaSource
      transitionFuel configuration projection fixedInstance decoder
      decoderBinding basis rc poseidon environment clean) :
    FixedK15EventBounds (exactCompilerJointLaw hiddenLaw parameters)
      (restrictFixedK15Events clean
        (exactPreQ16RestoredFixedK15Events environment)) := by
  refine ⟨fun kind ↦ ?_⟩
  by_cases semantic : kind = .semantic
  · subst kind
    exact (exact_tag73_restricted_preQ16_semantic_probability_le_of_source
      hiddenLaw clean semanticLanes semanticTerminal semanticSumcheck
      semanticCovered).trans (ordinary_bound_le_common_nonzero_bound 30500)
  · by_cases relation : kind = .relationAlpha
    · subst kind
      exact
        (exact_tag73_restricted_preQ16_relation_alpha_probability_le_of_source
          hiddenLaw clean relationSource).trans
            (ordinary_bound_le_common_nonzero_bound 24)
    · exact remaining.category kind semantic relation

#print axioms exact_tag73_restricted_preQ16_semantic_probability_le_of_source
#print axioms restricted_preQ16_fixed_k15_event_bounds_of_semantic_relation_sources

end
end AspisK1.V7Tag73PreQ16K15RestrictedSemanticActualLawClosure
