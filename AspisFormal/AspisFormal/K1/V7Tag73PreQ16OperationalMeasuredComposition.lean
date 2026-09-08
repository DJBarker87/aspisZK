import AspisFormal.K1.V7Tag73ExactMeasuredCleanK16Assembly
import AspisFormal.K1.V7Tag73PreQ16OperationalStageEvents

/-!
# Measured composition for the corrected pre-q16 operational stages

This file performs only event algebra.  Every numerical premise names one
literal event; no independence or grinding normalization is used.  The
pre-q16 late-target term is kept explicit because it was not part of the old
completed-transcript K1.3 ledger.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16OperationalMeasuredComposition

open MeasureTheory
open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK12Bound
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K12ExactFailureProbability
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16TargetProbability
open AspisK1.V7Tag73K13PreQ16TargetSchedulerTree
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73PreQ16OperationalStageAssembly
open AspisK1.V7Tag73PreQ16OperationalStageEvents
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Exact causal target term introduced by resolving Merkle paths at the
chronological pre-q16 prefix. -/
def exactPreQ16LateTargetRawError
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  ((((preQ16MerkleTargetCapsFrom 0
          (unifiedFull256ExposureCap parameters)).sum) *
      (2 ^ 256) ^ (unifiedFull256ExposureCap parameters - 1) : Nat) :
      ENNReal) /
    (((2 : ENNReal) ^ 256) ^ unifiedFull256ExposureCap parameters)

/-- Complete raw error for corrected chronological K1.3. -/
def exactPreQ16OperationalK13RawError
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  q16SemanticOneForestRawError + exactOneFoldIdealRawError +
    exactJointQueryBatchIdealRawError + exactLaterRelationAlphaIdealRawError +
      exactPreQ16LateTargetRawError parameters

/-- K1.2 bound for the corrected stage package. -/
theorem exact_preQ16_operational_k12_error_measure_bound
    {HiddenTape TapeIdentity Observation Payload : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
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
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (environment : ExactPreQ16OperationalStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (source : ExactTag73K12SourceObligations transitionFuel configuration
      projection fixedInstance) :
    K12TwoTreeMerkle208ErrorMeasureBound hiddenLaw
      (exactTag73PreQ16OperationalStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon transitionRoom
        programmedCover initialEncoderExact environment)
      (exactTag73K12ErrorBound configuration) := by
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (k12TwoTreeMerkle208ErrorEvent
          (exactTag73PreQ16OperationalStages transitionFuel configuration
            projection fixedInstance decoder decoderBinding basis rc poseidon
            transitionRoom programmedCover initialEncoderExact environment)) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactPrefixK12ClassifiedErrorEvent transitionFuel configuration
          projection fixedInstance) :=
      measure_mono
        (preQ16_operational_k12_error_subset_exact_classified_event
          transitionFuel configuration projection fixedInstance decoder
          decoderBinding basis rc poseidon transitionRoom programmedCover
          initialEncoderExact environment source)
    _ ≤ exactTag73K12ErrorBound configuration :=
      exact_prefix_k12_classified_error_probability_le hiddenLaw transitionFuel
        configuration projection fixedInstance transitionRoom

/-- Exact five-event K1.3 composition on the clean K1.6 slice. -/
theorem exact_preQ16_operational_k13_clean_error_measure_bound
    {HiddenTape TapeIdentity Observation Payload : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
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
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (environment : ExactPreQ16OperationalStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder)
    (q16Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactPreQ16K13JointTrialUnion transitionFuel configuration
              projection fixedInstance decoder) ≤ q16SemanticOneForestRawError)
    (oneFoldBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          ((exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
                projection fixedInstance \
              exactK13PreQ16MerkleTargetHitEvent configuration
                transitionFuel) ∩
            exactPreQ16K13OneFoldEvent transitionFuel configuration projection
              fixedInstance decoder) ≤ exactOneFoldIdealRawError)
    (jointBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactTag73K13JointQueryBatchCollisionEvent transitionFuel
              configuration projection fixedInstance decoder source) ≤
        exactJointQueryBatchIdealRawError)
    (laterBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactTag73K13LaterRelationAlphaEvent transitionFuel configuration
              projection fixedInstance decoder source) ≤
        exactLaterRelationAlphaIdealRawError)
    (lateTargetBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactK13PreQ16MerkleTargetHitEvent configuration transitionFuel) ≤
        exactPreQ16LateTargetRawError parameters) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          k13CircleListDecodeErrorEvent
            (exactTag73PreQ16OperationalStages transitionFuel configuration
              projection fixedInstance decoder decoderBinding basis rc poseidon
              transitionRoom programmedCover initialEncoderExact environment)) ≤
      exactPreQ16OperationalK13RawError parameters := by
  let law := exactCompilerJointLaw hiddenLaw parameters
  let clean := exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
    projection fixedInstance
  let q16 := exactPreQ16K13JointTrialUnion transitionFuel configuration
    projection fixedInstance decoder
  let oneFold := exactPreQ16K13OneFoldEvent transitionFuel configuration
    projection fixedInstance decoder
  let joint := exactTag73K13JointQueryBatchCollisionEvent transitionFuel
    configuration projection fixedInstance decoder source
  let later := exactTag73K13LaterRelationAlphaEvent transitionFuel configuration
    projection fixedInstance decoder source
  let late := exactK13PreQ16MerkleTargetHitEvent configuration transitionFuel
  have covered : clean ∩ k13CircleListDecodeErrorEvent
        (exactTag73PreQ16OperationalStages transitionFuel configuration
          projection fixedInstance decoder decoderBinding basis rc poseidon
          transitionRoom programmedCover initialEncoderExact environment) ⊆
      ((((clean ∩ q16) ∪ ((clean \ late) ∩ oneFold)) ∪ (clean ∩ joint)) ∪
        (clean ∩ later)) ∪ (clean ∩ late) := by
    rintro sample ⟨cleanMember, errorMember⟩
    have named := preQ16_operational_k13_error_subset_named_events
      transitionFuel configuration projection fixedInstance decoder
      decoderBinding basis rc poseidon transitionRoom programmedCover
      initialEncoderExact environment source errorMember
    rcases named with (((q16Member | oneFoldMember) | jointMember) |
        laterMember) | lateMember
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨cleanMember, q16Member⟩)))
    · by_cases lateMember : sample ∈ late
      · exact Or.inr ⟨cleanMember, lateMember⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inr
          ⟨⟨cleanMember, lateMember⟩, oneFoldMember⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨cleanMember, jointMember⟩))
    · exact Or.inl (Or.inr ⟨cleanMember, laterMember⟩)
    · exact Or.inr ⟨cleanMember,
        exact_k13_preQ16_late_target_subset_hit_event transitionFuel
          configuration projection fixedInstance transitionRoom lateMember⟩
  calc
    law.toOuterMeasure (clean ∩ k13CircleListDecodeErrorEvent
        (exactTag73PreQ16OperationalStages transitionFuel configuration
          projection fixedInstance decoder decoderBinding basis rc poseidon
          transitionRoom programmedCover initialEncoderExact environment)) ≤
      law.toOuterMeasure (((((clean ∩ q16) ∪ ((clean \ late) ∩ oneFold)) ∪
        (clean ∩ joint)) ∪ (clean ∩ later)) ∪ (clean ∩ late)) :=
      law.toOuterMeasure.mono covered
    _ ≤ law.toOuterMeasure ((((clean ∩ q16) ∪ ((clean \ late) ∩ oneFold)) ∪
          (clean ∩ joint)) ∪ (clean ∩ later)) +
        law.toOuterMeasure (clean ∩ late) := measure_union_le _ _
    _ ≤ (law.toOuterMeasure (((clean ∩ q16) ∪ ((clean \ late) ∩ oneFold)) ∪
          (clean ∩ joint)) + law.toOuterMeasure (clean ∩ later)) +
        law.toOuterMeasure (clean ∩ late) :=
      add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ((law.toOuterMeasure ((clean ∩ q16) ∪ ((clean \ late) ∩ oneFold)) +
          law.toOuterMeasure (clean ∩ joint)) +
          law.toOuterMeasure (clean ∩ later)) +
        law.toOuterMeasure (clean ∩ late) :=
      add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
    _ ≤ (((law.toOuterMeasure (clean ∩ q16) +
          law.toOuterMeasure ((clean \ late) ∩ oneFold)) +
          law.toOuterMeasure (clean ∩ joint)) +
          law.toOuterMeasure (clean ∩ later)) +
        law.toOuterMeasure (clean ∩ late) :=
      add_le_add
        (add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl) le_rfl
    _ ≤ (((q16SemanticOneForestRawError + exactOneFoldIdealRawError) +
          exactJointQueryBatchIdealRawError) +
          exactLaterRelationAlphaIdealRawError) +
        exactPreQ16LateTargetRawError parameters :=
      add_le_add
        (add_le_add (add_le_add (add_le_add q16Bound oneFoldBound) jointBound)
          laterBound) lateTargetBound
    _ = exactPreQ16OperationalK13RawError parameters := by
      unfold exactPreQ16OperationalK13RawError
      ac_rfl

/-- Corrected K1.4 composition from its exact pre-q16 width-29 event. -/
theorem exact_preQ16_operational_k14_clean_error_measure_bound
    {HiddenTape TapeIdentity Observation Payload : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
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
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (environment : ExactPreQ16OperationalStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (width29Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactPreQ16K14Width29Event transitionFuel configuration projection
              fixedInstance decoder) ≤ exactK14IdealRawError) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          k14CoherentChainErrorEvent
            (exactTag73PreQ16OperationalStages transitionFuel configuration
              projection fixedInstance decoder decoderBinding basis rc poseidon
              transitionRoom programmedCover initialEncoderExact environment)) ≤
      exactK14IdealRawError := by
  apply (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono ?_ |>.trans
    width29Bound
  rintro sample ⟨cleanMember, errorMember⟩
  exact ⟨cleanMember,
    preQ16_operational_k14_error_subset_width29 transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon
      transitionRoom programmedCover initialEncoderExact environment errorMember⟩

#print axioms exact_preQ16_operational_k12_error_measure_bound
#print axioms exact_preQ16_operational_k13_clean_error_measure_bound
#print axioms exact_preQ16_operational_k14_clean_error_measure_bound

end

end AspisK1.V7Tag73PreQ16OperationalMeasuredComposition
