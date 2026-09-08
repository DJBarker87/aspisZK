import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events
import AspisFormal.K1.V7Tag73K15RestrictedRelationAlphaActualLawClosure
import AspisFormal.K1.V7Tag73K13IdealErrorLedger
import AspisFormal.K1.V7Tag73RelationTailSourceComposition

/-!
# Compiler-clean actual-law closure for later Tag-73 relation alphas

Only relation rounds one through three can repair the post-query discrepancy.
This module indexes those three rounds directly, routes each through its exact
deployed pre-answer coordinates, and derives the `18 / (|QM31|-1)` ledger
entry from three degree-six root sets.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73K13RestrictedLaterAlphaActualLawClosure

open Module
open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisK1.V7Tag73K15FixedActualLawAdapters
open AspisK1.V7Tag73K15FixedSamplerProbabilityAdapters
open AspisK1.V7Tag73K15OrdinaryDuplexCoordinates
open AspisK1.V7Tag73K15RelationAlphaActualLawClosure
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73RelationTailSourceComposition
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7RelationCandidateBinding
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The three strictly positive relation rounds. -/
def laterRelationRound (tail : Fin 3) : Fin 4 :=
  ⟨tail.val + 1, by omega⟩

/-- Round-local spelling of the corrected K1.3 later-alpha event. -/
def exactTag73K13LaterRelationAlphaRoundEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder)
    (tail : Fin 3) : Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (_k12 : ExactPrefixK12Certificate input),
    (source.execution sample input).discrepancyTrace.AlphaRepair
      (laterRelationRound tail)}

theorem exact_tag73_k13_later_alpha_event_eq_iUnion
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) :
    exactTag73K13LaterRelationAlphaEvent transitionFuel configuration projection
        fixedInstance decoder source =
      ⋃ tail : Fin 3,
        exactTag73K13LaterRelationAlphaRoundEvent transitionFuel configuration
          projection fixedInstance decoder source tail := by
  ext sample
  constructor
  · rintro ⟨input, k12, round, positive, failure⟩
    let tail : Fin 3 := ⟨round.val - 1, by omega⟩
    have roundExact : laterRelationRound tail = round := by
      apply Fin.ext
      simp [laterRelationRound, tail]
      omega
    exact Set.mem_iUnion_of_mem tail ⟨input, k12, roundExact ▸ failure⟩
  · rintro member
    rcases Set.mem_iUnion.mp member with ⟨tail, input, k12, failure⟩
    exact ⟨input, k12, laterRelationRound tail, by
      simp [laterRelationRound], failure⟩

/-- The literal relation execution projected to exactly the claimed and
honest coefficient vectors fixed before one later alpha answer.  The current
alpha is absent from this source view. -/
def exactLaterAlphaPreChallengeView
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (relationSource : ExactTag73RelationSourceEnvironment transitionFuel
      configuration projection fixedInstance decoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (tail : Fin 3) : RelationAlphaPreChallengeView QM31Exact :=
  relationAlphaPreChallengeView
    (relationSource.run sample input).execution (laterRelationRound tail)

/-- Deterministic pre-alpha data for the three later rounds on one clean
slice. -/
structure ExactTag73RestrictedK13LaterAlphaSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (relationSource : ExactTag73RelationSourceEnvironment transitionFuel
      configuration projection fixedInstance decoder)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  view : Fin 3 → HiddenTape →
    FreshAnswerTape Digest256 (relationAlphaRouterResidual parameters) →
      Tag73CompleteOrdinarySamplerSkeleton →
        RelationAlphaPreChallengeView QM31Exact
  covered : ∀ tail hidden,
    jointEventSlice
        (clean ∩ exactTag73K13LaterRelationAlphaRoundEvent transitionFuel
          configuration projection fixedInstance decoder
            (relationSource.toK13SourceObligations transitionFuel configuration
              projection fixedInstance decoder) tail)
        hidden ⊆
      (exactPlainRomRelationAlphaSamplerCoordinates (laterRelationRound tail)
          transitionFuel configuration hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent Tag73DuplexOrdinarySucceeds
          (fun residual ↦ successfulTag73DuplexOrdinaryCoordinates ⁻¹'
            fixedOrdinarySamplerTargetEvent (fun skeleton ↦
              guardedRelationAlphaPreChallengeTarget
                (view tail hidden residual skeleton)))

/-- Exact compiler-law later-alpha bound on the clean slice. -/
theorem exact_tag73_restricted_k13_later_alpha_probability_le
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
    (relationSource : ExactTag73RelationSourceEnvironment transitionFuel
      configuration projection fixedInstance decoder)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (source : ExactTag73RestrictedK13LaterAlphaSource transitionFuel
      configuration projection fixedInstance decoder relationSource clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73K13LaterRelationAlphaEvent transitionFuel
          configuration projection fixedInstance decoder
            (relationSource.toK13SourceObligations transitionFuel configuration
              projection fixedInstance decoder)) ≤
      exactLaterRelationAlphaIdealRawError := by
  let k13Source := relationSource.toK13SourceObligations transitionFuel
    configuration projection fixedInstance decoder
  have roundBound : ∀ tail : Fin 3,
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ exactTag73K13LaterRelationAlphaRoundEvent transitionFuel
            configuration projection fixedInstance decoder k13Source tail) ≤
        (6 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
    intro tail
    apply exact_compiler_joint_law_dependent_ordinary_event_probability_le
      hiddenLaw parameters Tag73DuplexOrdinarySucceeds
      (exactPlainRomRelationAlphaSamplerCoordinates (laterRelationRound tail)
        transitionFuel configuration)
      successfulTag73DuplexOrdinaryCoordinates
      (fun hidden residual skeleton ↦ guardedRelationAlphaPreChallengeTarget
        (source.view tail hidden residual skeleton)) 6
    · intro hidden residual skeleton
      exact guardedRelationAlphaPreChallengeTarget_card_le_six
        (source.view tail hidden residual skeleton)
    · exact source.covered tail
  have covered : clean ∩
      exactTag73K13LaterRelationAlphaEvent transitionFuel configuration
        projection fixedInstance decoder k13Source ⊆
      ⋃ tail : Fin 3,
        clean ∩ exactTag73K13LaterRelationAlphaRoundEvent transitionFuel
          configuration projection fixedInstance decoder k13Source tail := by
    intro sample member
    rcases member with ⟨cleanMember, laterMember⟩
    rw [exact_tag73_k13_later_alpha_event_eq_iUnion transitionFuel
      configuration projection fixedInstance decoder k13Source] at laterMember
    rcases Set.mem_iUnion.mp laterMember with ⟨tail, tailMember⟩
    exact Set.mem_iUnion_of_mem tail ⟨cleanMember, tailMember⟩
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73K13LaterRelationAlphaEvent transitionFuel
          configuration projection fixedInstance decoder k13Source) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ tail : Fin 3,
          clean ∩ exactTag73K13LaterRelationAlphaRoundEvent transitionFuel
            configuration projection fixedInstance decoder k13Source tail) :=
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono covered
    _ ≤ ∑ tail : Fin 3,
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ exactTag73K13LaterRelationAlphaRoundEvent transitionFuel
            configuration projection fixedInstance decoder k13Source tail) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _tail : Fin 3,
        (6 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
      exact Finset.sum_le_sum fun tail _ ↦ roundBound tail
    _ = (18 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
      simp [div_eq_mul_inv]
      ring
    _ ≤ (18 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) :=
      ordinary_bound_le_common_nonzero_bound 18
    _ = exactLaterRelationAlphaIdealRawError := rfl

#print axioms laterRelationRound
#print axioms exact_tag73_k13_later_alpha_event_eq_iUnion
#print axioms ExactTag73RestrictedK13LaterAlphaSource
#print axioms exact_tag73_restricted_k13_later_alpha_probability_le

end
end AspisK1.V7Tag73K13RestrictedLaterAlphaActualLawClosure
