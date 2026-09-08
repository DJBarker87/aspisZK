import AspisFormal.K1.V7Tag73K15FixedCategoryCoordinateInclusions
import AspisFormal.K1.V7Tag73K15RestrictedSemanticActualLawClosure
import AspisFormal.K1.V7Tag73CausalGammaPrefixCoordinates
import AspisFormal.K1.V7Tag73PreQ16RestoredK15Events

/-!
# Actual-law adapters for the six remaining corrected pre-q16 K1.5 families

This module converts deterministic exact-compiler coordinate covers into the
six probability bounds not supplied by the semantic and relation-alpha
closures.  No probability inequality is stored in the source record.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16K15RemainingFixedActualLawClosure

open Module
open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
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
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73K15RestrictedMeasureLedger
open AspisK1.V7Tag73K15SemanticActualLawClosure
open AspisK1.V7Tag73PreQ16RestoredK15Context
open AspisK1.V7Tag73PreQ16RestoredK15Events
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatProbability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7FixedC1CopyCollisionSecurity
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7K15IndependentRootCertificates
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV5RelationSumcheckSoundness

noncomputable section

abbrev ExactPreQ16OrdinaryResidual (parameters : ExactCompilerResourceParameters) :=
  FreshAnswerTape Digest256 (relationAlphaRouterResidual parameters)

def Tag73DuplexOrdinaryPairSucceeds
    (tape : TotalTag73DuplexOrdinaryTape × TotalTag73DuplexOrdinaryTape) : Prop :=
  Tag73DuplexOrdinarySucceeds tape.1 ∧ Tag73DuplexOrdinarySucceeds tape.2

instance (tape : TotalTag73DuplexOrdinaryTape ×
    TotalTag73DuplexOrdinaryTape) :
    Decidable (Tag73DuplexOrdinaryPairSucceeds tape) := by
  unfold Tag73DuplexOrdinaryPairSucceeds
  infer_instance

def successfulTag73DuplexOrdinaryPairCoordinates :
    {tape : TotalTag73DuplexOrdinaryTape × TotalTag73DuplexOrdinaryTape //
      Tag73DuplexOrdinaryPairSucceeds tape} ≃
      SuccessfulTag73DuplexOrdinaryPair where
  toFun tape :=
    (successfulTag73DuplexOrdinaryCoordinates ⟨tape.1.1, tape.2.1⟩,
      successfulTag73DuplexOrdinaryCoordinates ⟨tape.1.2, tape.2.2⟩)
  invFun sample :=
    ⟨(successfulTag73DuplexOrdinaryCoordinates.symm sample.1,
        successfulTag73DuplexOrdinaryCoordinates.symm sample.2),
      successfulTag73DuplexOrdinaryCoordinates.symm sample.1 |>.property,
      successfulTag73DuplexOrdinaryCoordinates.symm sample.2 |>.property⟩
  left_inv := by
    intro tape
    apply Subtype.ext
    simp
  right_inv := by
    intro sample
    simp

noncomputable instance :
    Nonempty {tape : TotalTag73DuplexOrdinaryTape ×
        TotalTag73DuplexOrdinaryTape //
      Tag73DuplexOrdinaryPairSucceeds tape} :=
  Nonempty.map successfulTag73DuplexOrdinaryPairCoordinates.symm inferInstance

def ordinaryPairRouterResidual (parameters : ExactCompilerResourceParameters) :
    Nat :=
  (exactCompilerTargetCaps parameters).length - 16

abbrev ExactPreQ16OrdinaryPairResidual
    (parameters : ExactCompilerResourceParameters) :=
  FreshAnswerTape Digest256 (ordinaryPairRouterResidual parameters)

/-- Exact coordinate covers for the six remaining fixed families.  Every
field is deterministic source data; no measure bound is assumed. -/
structure ExactTag73RestrictedPreQ16RemainingFixedSources
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
  copyLambdaCoordinates : HiddenTape →
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactPreQ16OrdinaryResidual parameters × TotalTag73DuplexOrdinaryTape
  copyLambdaLanes : HiddenTape → ExactPreQ16OrdinaryResidual parameters →
    C1InitialWords
  copyLambdaCovered : ∀ hidden, jointEventSlice
      (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event
        .copyLambda) hidden ⊆
    copyLambdaCoordinates hidden ⁻¹'
      dependentSuccessfulSubtypeEvent Tag73DuplexOrdinarySucceeds
        (fun residual ↦ successfulTag73DuplexOrdinaryCoordinates ⁻¹'
          fixedOrdinarySamplerTargetEvent (fun _ ↦
            familyLambdaBad (fixedC1CopySourceFamily decoder
              (copyLambdaLanes hidden residual))))
  copyChiCoordinates : HiddenTape →
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactPreQ16OrdinaryResidual parameters × TotalTag73DuplexOrdinaryTape
  copyChiLanes : HiddenTape → ExactPreQ16OrdinaryResidual parameters →
    C1InitialWords
  copyChiLambda : HiddenTape → ExactPreQ16OrdinaryResidual parameters →
    QM31Exact
  copyChiCovered : ∀ hidden, jointEventSlice
      (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event
        .copyChi) hidden ⊆
    copyChiCoordinates hidden ⁻¹'
      dependentSuccessfulSubtypeEvent Tag73DuplexOrdinarySucceeds
        (fun residual ↦ successfulTag73DuplexOrdinaryCoordinates ⁻¹'
          fixedOrdinarySamplerTargetEvent (fun _ ↦
            familyChiBad (fixedC1CopySourceFamily decoder
              (copyChiLanes hidden residual)) (copyChiLambda hidden residual)))
  muCoordinates : HiddenTape →
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactPreQ16OrdinaryResidual parameters × TotalTag73DuplexOrdinaryTape
  muCovered : ∀ hidden, jointEventSlice
      (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event
        .muZero) hidden ⊆
    muCoordinates hidden ⁻¹'
      dependentSuccessfulSubtypeEvent Tag73DuplexOrdinarySucceeds
        (fun _ ↦ successfulTag73DuplexOrdinaryCoordinates ⁻¹'
          fixedOrdinarySamplerTargetEvent (fun _ ↦ zeroChallengeSet))
  inactiveChiCoordinates : HiddenTape →
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactPreQ16OrdinaryResidual parameters × TotalTag73DuplexOrdinaryTape
  inactiveChiCovered : ∀ hidden, jointEventSlice
      (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event
        .inactiveChi) hidden ⊆
    inactiveChiCoordinates hidden ⁻¹'
      dependentSuccessfulSubtypeEvent Tag73DuplexOrdinarySucceeds
        (fun _ ↦ successfulTag73DuplexOrdinaryCoordinates ⁻¹'
          fixedOrdinarySamplerTargetEvent (fun _ ↦ zeroChallengeSet))
  oodCoordinates : HiddenTape →
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactPreQ16OrdinaryPairResidual parameters ×
        (TotalTag73DuplexOrdinaryTape × TotalTag73DuplexOrdinaryTape)
  oodTrace : HiddenTape → ExactPreQ16OrdinaryPairResidual parameters →
    Tag73CompleteOrdinaryPairSkeleton →
      FourRoundDiscrepancyTrace QM31Exact
  oodCovered : ∀ hidden, jointEventSlice
      (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event
        .oodMix) hidden ⊆
    oodCoordinates hidden ⁻¹'
      dependentSuccessfulSubtypeEvent Tag73DuplexOrdinaryPairSucceeds
        (fun residual ↦ successfulTag73DuplexOrdinaryPairCoordinates ⁻¹'
          duplexOrdinaryPairDependentEvent
            (fixedOodMixPairTarget (oodTrace hidden residual) 0))
  kappaCoordinates : HiddenTape →
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerGammaPrefixResidual parameters × TotalGammaDuplexTape
  kappaValues : HiddenTape → ExactCompilerGammaPrefixResidual parameters →
    VariableGammaCompleteSkeleton → Fin 3 → QM31Exact
  kappaCovered : ∀ hidden, jointEventSlice
      (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event
        .kappaPointRow) hidden ⊆
    kappaCoordinates hidden ⁻¹'
      dependentSuccessfulSubtypeEvent GammaPrefixSucceeds
        (fun residual ↦ successfulGammaPrefixSkeletonDependentEvent
          (guardedVariablePrefixKappaCollisionTarget
            (kappaValues hidden residual)))

theorem remaining_preQ16_fixed_k15_event_bounds_of_sources
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
    (source : ExactTag73RestrictedPreQ16RemainingFixedSources transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon environment clean) :
    FixedK15EventBoundsExceptSemanticRelationAlpha
      (exactCompilerJointLaw hiddenLaw parameters)
      (restrictFixedK15Events clean
        (exactPreQ16RestoredFixedK15Events environment)) := by
  have lambdaBound := exact_compiler_joint_law_copy_lambda_event_probability_le
    hiddenLaw parameters decoder Tag73DuplexOrdinarySucceeds
    source.copyLambdaCoordinates successfulTag73DuplexOrdinaryCoordinates
    source.copyLambdaLanes
    (clean ∩
      (exactPreQ16RestoredFixedK15Events environment).event .copyLambda)
    source.copyLambdaCovered
  have chiBound := exact_compiler_joint_law_copy_chi_event_probability_le
    hiddenLaw parameters decoder Tag73DuplexOrdinarySucceeds
    source.copyChiCoordinates successfulTag73DuplexOrdinaryCoordinates
    source.copyChiLanes source.copyChiLambda
    (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event .copyChi)
    source.copyChiCovered
  have muBound := exact_compiler_joint_law_zero_ordinary_event_probability_le
    hiddenLaw parameters Tag73DuplexOrdinarySucceeds source.muCoordinates
    successfulTag73DuplexOrdinaryCoordinates
    (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event .muZero)
    source.muCovered
  have inactiveBound :=
    exact_compiler_joint_law_zero_ordinary_event_probability_le hiddenLaw
      parameters Tag73DuplexOrdinarySucceeds source.inactiveChiCoordinates
      successfulTag73DuplexOrdinaryCoordinates
      (clean ∩
        (exactPreQ16RestoredFixedK15Events environment).event .inactiveChi)
      source.inactiveChiCovered
  have oodBound := exact_compiler_joint_law_ood_mix_event_probability_le
    hiddenLaw parameters Tag73DuplexOrdinaryPairSucceeds source.oodCoordinates
    successfulTag73DuplexOrdinaryPairCoordinates source.oodTrace 0
    (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event .oodMix)
    source.oodCovered
  have kappaBound :=
    exact_compiler_joint_law_guarded_kappa_event_probability_le hiddenLaw
      parameters source.kappaCoordinates source.kappaValues
      (clean ∩
        (exactPreQ16RestoredFixedK15Events environment).event .kappaPointRow)
      source.kappaCovered
  have ordinaryOneBound :
      (1 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) ≤
        (1 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
    apply ENNReal.div_le_div_left
    exact_mod_cast Nat.sub_le (P ^ 4) 1
  refine ⟨fun kind notSemantic notRelation ↦ ?_⟩
  cases kind with
  | semantic => exact False.elim (notSemantic rfl)
  | copyLambda =>
      change (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event
          .copyLambda) ≤ _
      simpa [fixedK15CategoryCap] using
        lambdaBound.trans (ordinary_bound_le_common_nonzero_bound 292800)
  | copyChi =>
      change (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event
          .copyChi) ≤ _
      simpa [fixedK15CategoryCap] using
        chiBound.trans (ordinary_bound_le_common_nonzero_bound 73100)
  | muZero =>
      have common := muBound.trans ordinaryOneBound
      simpa only [restrictFixedK15Events, fixedK15CategoryCap,
        Nat.cast_one] using common
  | inactiveChi =>
      have common := inactiveBound.trans ordinaryOneBound
      simpa only [restrictFixedK15Events, fixedK15CategoryCap,
        Nat.cast_one] using common
  | oodMix =>
      change (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event
          .oodMix) ≤ _
      simpa [fixedK15CategoryCap] using
        oodBound.trans (ordinary_bound_le_common_nonzero_bound 2)
  | relationAlpha => exact False.elim (notRelation rfl)
  | kappaPointRow =>
      change (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ (exactPreQ16RestoredFixedK15Events environment).event
          .kappaPointRow) ≤ _
      simpa [fixedK15CategoryCap] using kappaBound

#print axioms successfulTag73DuplexOrdinaryPairCoordinates
#print axioms ExactTag73RestrictedPreQ16RemainingFixedSources
#print axioms remaining_preQ16_fixed_k15_event_bounds_of_sources

end
end AspisK1.V7Tag73PreQ16K15RemainingFixedActualLawClosure
