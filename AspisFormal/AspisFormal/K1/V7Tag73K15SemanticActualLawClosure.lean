import AspisFormal.K1.V7Tag73ExactRestoredK15Events
import AspisFormal.K1.V7Tag73K15RelationAlphaActualLawClosure
import AspisFormal.K1.V7Tag73K15SemanticActualLawAdapter

/-! Actual-law closure for the fixed-family Tag-73 semantic category. -/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K15SemanticActualLawClosure

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
open AspisK1.V7Tag73K15RelationAlphaActualLawClosure
open AspisK1.V7Tag73K15SemanticActualLawAdapter
open AspisK1.V7Tag73K15SemanticFamilyProbability
open AspisK1.V7Tag73K15SemanticSamplerFactorization
open AspisK1.V7Tag73K15SemanticSamplerFamilyProbability
open AspisK1.V7Tag73K15SemanticSequentialRouter
open AspisK1.V7Tag73RestoredCausalK15Stage
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7RelationCandidateBinding
open AspisPool.V7Width29ComponentExtraction
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound

noncomputable section

abbrev ExactTag73SemanticResidual (parameters : ExactCompilerResourceParameters) :=
  FreshAnswerTape Digest256 (semanticRouterResidual parameters)

/-- Initial words fixed before semantic values are exposed.  These are named
types, rather than fields of one enormous dependent record, to keep generated
projection terms small enough for Lean's serializer. -/
def ExactTag73SemanticLanes
    (HiddenTape : Type) (parameters : ExactCompilerResourceParameters) : Type :=
  HiddenTape → ExactTag73SemanticResidual parameters →
    SemanticOrdinarySkeletonFamily → Width29InitialWords QM31Exact

def ExactTag73SemanticTerminal
    (HiddenTape : Type) (parameters : ExactCompilerResourceParameters)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : ExactTag73SemanticLanes HiddenTape parameters) : Type :=
  ∀ hidden residual skeleton,
    FixedWidth29TupleCandidate decoder (lanes hidden residual skeleton) →
      FixedTerminalAlgebraPlan QM31Exact

def ExactTag73SemanticSumcheck
    (HiddenTape : Type) (parameters : ExactCompilerResourceParameters)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : ExactTag73SemanticLanes HiddenTape parameters) : Type :=
  ∀ hidden residual skeleton,
    FixedWidth29TupleCandidate decoder (lanes hidden residual skeleton) →
      AdaptiveDegree27MessagePlan QM31Exact

/-- Deterministic inclusion of the literal semantic event in the exact
22-sampler coordinate event. -/
def ExactTag73SemanticCover
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
    (lanes : ExactTag73SemanticLanes HiddenTape parameters)
    (terminal : ExactTag73SemanticTerminal HiddenTape parameters decoder lanes)
    (sumcheck : ExactTag73SemanticSumcheck HiddenTape parameters decoder lanes) :
    Prop :=
  ∀ hidden, jointEventSlice
      ((exactTag73RestoredFixedK15Events environment).event .semantic) hidden ⊆
    (exactPlainRomSemanticSamplerCoordinates transitionFuel configuration
      hidden) ⁻¹'
      dependentSuccessfulSubtypeEvent AllSemanticDuplexSamplersSucceed
        (fun residual ↦ successfulSemanticSamplerFamilyCoordinates ⁻¹'
          semanticSkeletonDependentEvent (fun skeleton ↦
            fixedWidth29SemanticValueEvent decoder
              (lanes hidden residual skeleton)
              (terminal hidden residual skeleton)
              (sumcheck hidden residual skeleton)))

/-- The literal semantic category under the exact compiler law costs at most
`30,500 / |QM31|`.  Its last four arguments are deterministic source data,
not probability premises. -/
theorem exact_tag73_semantic_probability_le_of_source
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
    (lanes : ExactTag73SemanticLanes HiddenTape parameters)
    (terminal : ExactTag73SemanticTerminal HiddenTape parameters decoder lanes)
    (sumcheck : ExactTag73SemanticSumcheck HiddenTape parameters decoder lanes)
    (covered : ExactTag73SemanticCover environment lanes terminal sumcheck) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        ((exactTag73RestoredFixedK15Events environment).event .semantic) ≤
      (30500 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  exact exact_compiler_joint_law_semantic_family_probability_le hiddenLaw
    parameters
    (exactPlainRomSemanticSamplerCoordinates transitionFuel configuration)
    decoder lanes terminal sumcheck
    ((exactTag73RestoredFixedK15Events environment).event .semantic)
    (by exact covered)

/-- Temporary six-category ledger after semantic and relation-alpha are
derived from their deterministic sources. -/
structure FixedK15EventBoundsExceptSemanticRelationAlpha
    {Coins : Type} (law : PMF Coins) (events : FixedK15Events Coins) : Prop where
  category : ∀ kind, kind ≠ .semantic → kind ≠ .relationAlpha →
    law.toOuterMeasure (events.event kind) ≤
      (fixedK15CategoryCap kind : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal)

theorem fixed_k15_event_bounds_of_semantic_relation_sources
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
    (remaining : FixedK15EventBoundsExceptSemanticRelationAlpha
      (exactCompilerJointLaw hiddenLaw parameters)
      (exactTag73RestoredFixedK15Events environment))
    (semanticLanes : ExactTag73SemanticLanes HiddenTape parameters)
    (semanticTerminal : ExactTag73SemanticTerminal HiddenTape parameters decoder
      semanticLanes)
    (semanticSumcheck : ExactTag73SemanticSumcheck HiddenTape parameters decoder
      semanticLanes)
    (semanticCovered : ExactTag73SemanticCover environment semanticLanes
      semanticTerminal semanticSumcheck)
    (relationSource : ExactTag73K15RelationAlphaSource transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon environment) :
    FixedK15EventBounds (exactCompilerJointLaw hiddenLaw parameters)
      (exactTag73RestoredFixedK15Events environment) := by
  refine ⟨fun kind ↦ ?_⟩
  by_cases semantic : kind = .semantic
  · subst kind
    exact (exact_tag73_semantic_probability_le_of_source hiddenLaw
      semanticLanes semanticTerminal semanticSumcheck semanticCovered).trans
        (ordinary_bound_le_common_nonzero_bound 30500)
  · by_cases relation : kind = .relationAlpha
    · subst kind
      exact (exact_tag73_relation_alpha_probability_le_of_source hiddenLaw
        relationSource).trans (ordinary_bound_le_common_nonzero_bound 24)
    · exact remaining.category kind semantic relation

#print axioms exact_tag73_semantic_probability_le_of_source
#print axioms FixedK15EventBoundsExceptSemanticRelationAlpha
#print axioms fixed_k15_event_bounds_of_semantic_relation_sources

end
end AspisK1.V7Tag73K15SemanticActualLawClosure
