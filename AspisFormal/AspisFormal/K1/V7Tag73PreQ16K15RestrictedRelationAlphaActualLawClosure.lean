import AspisFormal.K1.V7Tag73K15RestrictedRelationAlphaActualLawClosure
import AspisFormal.K1.V7Tag73PreQ16RestoredK15Events

/-!
# Actual-law relation-alpha closure for corrected pre-q16 K1.5

This is the four-round degree-six root argument indexed by the corrected
chronological K1.3 words and coherent K1.4 extraction.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16K15RestrictedRelationAlphaActualLawClosure

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
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisK1.V7Tag73K15FixedActualLawAdapters
open AspisK1.V7Tag73K15FixedSamplerProbabilityAdapters
open AspisK1.V7Tag73K15OrdinaryDuplexCoordinates
open AspisK1.V7Tag73K15RelationAlphaActualLawClosure
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73PreQ16RestoredK15Context
open AspisK1.V7Tag73PreQ16RestoredK15Events
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

/-- One corrected relation-alpha round before taking the four-round union. -/
def exactPreQ16RestoredRelationAlphaRoundEvent
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
    (round : Fin 4) : Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ context : ExactPreQ16K15Context transitionFuel configuration
      projection fixedInstance decoder decoderBinding,
    context.sample = sample ∧
      (context.material
        environment.operational).data.execution.discrepancyTrace.AlphaRepair
          round}

theorem exactPreQ16Restored_relationAlpha_event_eq_iUnion
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
      projection fixedInstance decoder decoderBinding basis rc poseidon) :
    (exactPreQ16RestoredFixedK15Events environment).event .relationAlpha =
      ⋃ round : Fin 4,
        exactPreQ16RestoredRelationAlphaRoundEvent environment round := by
  ext sample
  simp only [exactPreQ16RestoredFixedK15Events,
    exactPreQ16FixedK15CategoryHolds, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨context, contextSample, round, failure⟩
    exact ⟨round, context, contextSample, failure⟩
  · rintro ⟨round, context, contextSample, failure⟩
    exact ⟨context, contextSample, round, failure⟩

/-- Deterministic pre-alpha executions and inclusions for all four rounds. -/
structure ExactTag73RestrictedPreQ16K15RelationAlphaSource
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
    (basis : Basis (Fin 4) F QM31Exact) (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (environment : ExactPreQ16RestoredK15Environment transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  execution : Fin 4 → HiddenTape →
    FreshAnswerTape Digest256 (relationAlphaRouterResidual parameters) →
      Tag73CompleteOrdinarySamplerSkeleton → CandidateExecution QM31Exact
  covered : ∀ round hidden,
    jointEventSlice
        (clean ∩ exactPreQ16RestoredRelationAlphaRoundEvent environment round)
        hidden ⊆
      (exactPlainRomRelationAlphaSamplerCoordinates round transitionFuel
          configuration hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent Tag73DuplexOrdinarySucceeds
          (fun residual ↦ successfulTag73DuplexOrdinaryCoordinates ⁻¹'
            fixedOrdinarySamplerTargetEvent (fun skeleton ↦
              guardedRelationAlphaTarget
                (execution round hidden residual skeleton) round))

theorem exact_tag73_restricted_preQ16_relation_alpha_probability_le_of_source
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
    (source : ExactTag73RestrictedPreQ16K15RelationAlphaSource transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon environment clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩
          (exactPreQ16RestoredFixedK15Events environment).event .relationAlpha) ≤
      (24 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  have roundBound : ∀ round : Fin 4,
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ exactPreQ16RestoredRelationAlphaRoundEvent environment
            round) ≤
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
  have covered :
      clean ∩
          (exactPreQ16RestoredFixedK15Events environment).event .relationAlpha ⊆
        ⋃ round : Fin 4,
          clean ∩ exactPreQ16RestoredRelationAlphaRoundEvent environment
            round := by
    intro sample member
    rcases member with ⟨cleanMember, relationMember⟩
    rw [exactPreQ16Restored_relationAlpha_event_eq_iUnion environment] at relationMember
    rcases Set.mem_iUnion.mp relationMember with ⟨round, roundMember⟩
    exact Set.mem_iUnion_of_mem round ⟨cleanMember, roundMember⟩
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩
          (exactPreQ16RestoredFixedK15Events environment).event .relationAlpha) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ round : Fin 4,
          clean ∩ exactPreQ16RestoredRelationAlphaRoundEvent environment
            round) :=
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono covered
    _ ≤ ∑ round : Fin 4,
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ exactPreQ16RestoredRelationAlphaRoundEvent environment
            round) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _round : Fin 4,
        (6 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
      exact Finset.sum_le_sum fun round _ ↦ roundBound round
    _ = (24 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
      simp [div_eq_mul_inv]
      ring

#print axioms exactPreQ16Restored_relationAlpha_event_eq_iUnion
#print axioms ExactTag73RestrictedPreQ16K15RelationAlphaSource
#print axioms exact_tag73_restricted_preQ16_relation_alpha_probability_le_of_source

end
end AspisK1.V7Tag73PreQ16K15RestrictedRelationAlphaActualLawClosure
