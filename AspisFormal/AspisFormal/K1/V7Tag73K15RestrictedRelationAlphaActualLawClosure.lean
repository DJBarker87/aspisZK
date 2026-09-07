import AspisFormal.K1.V7Tag73K15RelationAlphaActualLawClosure

/-!
# Compiler-clean actual-law closure for Tag-73 relation-alpha

The four degree-six relation-alpha targets are bounded only on the legal
same-tape slice consumed by K1.6.  This preserves the exact `24 / |QM31|`
bound and does not classify adversary-first cache population as a bad event.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73K15RestrictedRelationAlphaActualLawClosure

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
open AspisK1.V7Tag73K15RelationAlphaActualLawClosure
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

/-- Deterministic pre-alpha data and event inclusion for each of the four
rounds, restricted to one compiler-clean slice. -/
structure ExactTag73RestrictedK15RelationAlphaSource
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
      poseidon)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  execution : Fin 4 → HiddenTape →
    FreshAnswerTape Digest256 (relationAlphaRouterResidual parameters) →
      Tag73CompleteOrdinarySamplerSkeleton → CandidateExecution QM31Exact
  covered : ∀ round hidden,
    jointEventSlice
        (clean ∩ exactTag73RestoredRelationAlphaRoundEvent environment round)
        hidden ⊆
      (exactPlainRomRelationAlphaSamplerCoordinates round transitionFuel
          configuration hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent Tag73DuplexOrdinarySucceeds
          (fun residual ↦ successfulTag73DuplexOrdinaryCoordinates ⁻¹'
            fixedOrdinarySamplerTargetEvent (fun skeleton ↦
              guardedRelationAlphaTarget
                (execution round hidden residual skeleton) round))

/-- Exact compiler-law bound for relation-alpha on the clean slice. -/
theorem exact_tag73_restricted_relation_alpha_probability_le_of_source
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
    (source : ExactTag73RestrictedK15RelationAlphaSource transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon environment clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩
          (exactTag73RestoredFixedK15Events environment).event .relationAlpha) ≤
      (24 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  have roundBound : ∀ round : Fin 4,
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ exactTag73RestoredRelationAlphaRoundEvent environment
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
          (exactTag73RestoredFixedK15Events environment).event .relationAlpha ⊆
        ⋃ round : Fin 4,
          clean ∩ exactTag73RestoredRelationAlphaRoundEvent environment
            round := by
    intro sample member
    rcases member with ⟨cleanMember, relationMember⟩
    rw [exactTag73Restored_relationAlpha_event_eq_iUnion environment] at relationMember
    rcases Set.mem_iUnion.mp relationMember with ⟨round, roundMember⟩
    exact Set.mem_iUnion_of_mem round ⟨cleanMember, roundMember⟩
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩
          (exactTag73RestoredFixedK15Events environment).event .relationAlpha) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ round : Fin 4,
          clean ∩ exactTag73RestoredRelationAlphaRoundEvent environment
            round) :=
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono covered
    _ ≤ ∑ round : Fin 4,
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ exactTag73RestoredRelationAlphaRoundEvent environment
            round) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _round : Fin 4,
        (6 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
      exact Finset.sum_le_sum fun round _ ↦ roundBound round
    _ = (24 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
      simp [div_eq_mul_inv]
      ring

#print axioms ExactTag73RestrictedK15RelationAlphaSource
#print axioms exact_tag73_restricted_relation_alpha_probability_le_of_source

end
end AspisK1.V7Tag73K15RestrictedRelationAlphaActualLawClosure
