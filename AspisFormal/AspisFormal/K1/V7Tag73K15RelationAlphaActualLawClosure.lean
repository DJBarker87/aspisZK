import AspisFormal.K1.V7Tag73ExactRestoredK15Events
import AspisFormal.K1.V7Tag73K15FixedActualLawAdapters
import AspisFormal.K1.V7Tag73K15OrdinaryDuplexCoordinates
import AspisFormal.K1.V7Tag73K15RelationAlphaPreAnswerRouters

/-!
# Actual-law closure for the four fixed K1.5 relation-alpha families

Each relation round has its own deployed pre-answer router.  This module
transports the degree-six root theorem through those exact coordinates and
then unions the four round events.  The remaining source record contains only
pre-alpha execution data and deterministic inclusion of the literal event.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73K15RelationAlphaActualLawClosure

open Module
open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredK15Events
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K15FixedActualLawAdapters
open AspisK1.V7Tag73K15FixedSamplerProbabilityAdapters
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisK1.V7Tag73K15OrdinaryDuplexCoordinates
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73RestoredCausalK15Stage
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7RelationCandidateBinding
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV5RelationSumcheckSoundness

noncomputable section

/-- Temporary ledger shape while the other seven fixed families are closed
one by one.  Unlike `FixedK15EventBounds`, it contains no relation-alpha
probability premise. -/
structure FixedK15EventBoundsExceptRelationAlpha
    {Coins : Type} (law : PMF Coins) (events : FixedK15Events Coins) : Prop where
  category : ∀ kind, kind ≠ .relationAlpha →
    law.toOuterMeasure (events.event kind) ≤
      (fixedK15CategoryCap kind : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal)

/-- A round-local event before taking the finite union stored in the K1.5
ledger. -/
def exactTag73RestoredRelationAlphaRoundEvent
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
    (round : Fin 4) : Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ context : ExactTag73K15Context transitionFuel configuration
      projection fixedInstance decoder decoderBinding,
    context.sample = sample ∧
      (context.material
        environment.operational).data.execution.discrepancyTrace.AlphaRepair
          round}

/-- The exact relation-alpha category is the union of its four round-local
events. -/
theorem exactTag73Restored_relationAlpha_event_eq_iUnion
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
      poseidon) :
    (exactTag73RestoredFixedK15Events environment).event .relationAlpha =
      ⋃ round : Fin 4,
        exactTag73RestoredRelationAlphaRoundEvent environment round := by
  ext sample
  simp only [exactTag73RestoredFixedK15Events,
    exactTag73FixedK15CategoryHolds, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨context, contextSample, round, failure⟩
    exact ⟨round, context, contextSample, failure⟩
  · rintro ⟨round, context, contextSample, failure⟩
    exact ⟨context, contextSample, round, failure⟩

/-- The degree-six target is empty unless the incoming claim is genuinely
wrong.  This makes the cardinality theorem total on every nuisance skeleton. -/
noncomputable def guardedRelationAlphaTarget
    (execution : CandidateExecution QM31Exact) (round : Fin 4) :
    Finset QM31Exact :=
  if _wrong : execution.incomingAt round ≠
      relationBoundary (execution.honestAt round) then
    execution.relationCollisionSet round
  else
    ∅

theorem guardedRelationAlphaTarget_card_le_six
    (execution : CandidateExecution QM31Exact) (round : Fin 4) :
    (guardedRelationAlphaTarget execution round).card ≤ 6 := by
  classical
  by_cases wrong : execution.incomingAt round ≠
      relationBoundary (execution.honestAt round)
  · simp only [guardedRelationAlphaTarget, dif_pos wrong]
    exact execution.relationCollisionSet_card_le_six round wrong
  · simp [guardedRelationAlphaTarget, wrong]

/-- Deterministic source seam for all four relation-alpha coordinates. -/
structure ExactTag73K15RelationAlphaSource
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters)
    (projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload)
    (fixedInstance : PublicInstance V5PublicStatement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (environment : ExactTag73RestoredCausalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) where
  execution : Fin 4 → HiddenTape →
    FreshAnswerTape Digest256 (relationAlphaRouterResidual parameters) →
      Tag73CompleteOrdinarySamplerSkeleton → CandidateExecution QM31Exact
  covered : ∀ round hidden,
    jointEventSlice
        (exactTag73RestoredRelationAlphaRoundEvent environment round) hidden ⊆
      (exactPlainRomRelationAlphaSamplerCoordinates round transitionFuel
          configuration hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent Tag73DuplexOrdinarySucceeds
          (fun residual ↦ successfulTag73DuplexOrdinaryCoordinates ⁻¹'
            fixedOrdinarySamplerTargetEvent (fun skeleton ↦
              guardedRelationAlphaTarget
                (execution round hidden residual skeleton) round))

/-- Actual compiler-law bound for the union of all four relation-alpha
failures.  No probability inequality is accepted by the source record. -/
theorem exact_tag73_relation_alpha_probability_le_of_source
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
    (source : ExactTag73K15RelationAlphaSource transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon
      environment) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        ((exactTag73RestoredFixedK15Events environment).event .relationAlpha) ≤
      (24 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  have roundBound : ∀ round : Fin 4,
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73RestoredRelationAlphaRoundEvent environment round) ≤
        (6 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
    intro round
    apply exact_compiler_joint_law_dependent_ordinary_event_probability_le
      hiddenLaw parameters Tag73DuplexOrdinarySucceeds
      (exactPlainRomRelationAlphaSamplerCoordinates round transitionFuel
        configuration)
      successfulTag73DuplexOrdinaryCoordinates
      (fun hidden residual skeleton ↦ guardedRelationAlphaTarget
        (source.execution round hidden residual skeleton) round)
      6
    · intro hidden residual skeleton
      exact guardedRelationAlphaTarget_card_le_six
        (source.execution round hidden residual skeleton) round
    · exact source.covered round
  rw [exactTag73Restored_relationAlpha_event_eq_iUnion environment]
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ round : Fin 4,
          exactTag73RestoredRelationAlphaRoundEvent environment round) ≤
      ∑ round : Fin 4,
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73RestoredRelationAlphaRoundEvent environment round) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _round : Fin 4,
        (6 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
      exact Finset.sum_le_sum fun round _ ↦ roundBound round
    _ = (24 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
      simp [div_eq_mul_inv]
      ring

/-- Install the actual-law relation-alpha result into the fixed-event ledger.
Only the other seven categories remain as independent obligations. -/
theorem fixed_k15_event_bounds_of_relation_alpha_source
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
    (remaining : FixedK15EventBoundsExceptRelationAlpha
      (exactCompilerJointLaw hiddenLaw parameters)
      (exactTag73RestoredFixedK15Events environment))
    (source : ExactTag73K15RelationAlphaSource transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon
      environment) :
    FixedK15EventBounds (exactCompilerJointLaw hiddenLaw parameters)
      (exactTag73RestoredFixedK15Events environment) := by
  refine ⟨fun kind ↦ ?_⟩
  by_cases relation : kind = .relationAlpha
  · subst kind
    exact (exact_tag73_relation_alpha_probability_le_of_source hiddenLaw
      source).trans (ordinary_bound_le_common_nonzero_bound 24)
  · exact remaining.category kind relation

#print axioms exactTag73Restored_relationAlpha_event_eq_iUnion
#print axioms guardedRelationAlphaTarget_card_le_six
#print axioms ExactTag73K15RelationAlphaSource
#print axioms exact_tag73_relation_alpha_probability_le_of_source
#print axioms FixedK15EventBoundsExceptRelationAlpha
#print axioms fixed_k15_event_bounds_of_relation_alpha_source

end

end AspisK1.V7Tag73K15RelationAlphaActualLawClosure
