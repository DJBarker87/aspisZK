import AspisFormal.K1.V7Tag73ExactConcreteK12Bound
import AspisFormal.K1.V7Tag73PreQ16OperationalStageAssembly

/-!
# Exact events for the corrected pre-q16 operational stages

The generic K1.6 interface measures inhabitation of each dependent error
family, not merely the branch selected by its classifier.  This module
therefore uses the narrow operational K1.3 error type and reduces every one
of its constructors to a literal chronological event.  The impossible
collision constructor is discharged by the preceding K1.2 certificate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16OperationalStageEvents

open MeasureTheory
open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK12Bound
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16TargetProbability
open AspisK1.V7Tag73K12ExactFailureProbability
open AspisK1.V7Tag73PreQ16OperationalStageAssembly
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- Union of all genuine corrected final-work/q16 trials. -/
def exactPreQ16K13JointTrialUnion
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  ⋃ trial : ExactCompilerExposureTrial parameters,
    exactPreQ16K13JointTrialEvent transitionFuel configuration projection
      fixedInstance decoder trial

/-- The one-fold error on the word fixed immediately before q16. -/
def exactPreQ16K13OneFoldEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (_k12 : ExactPrefixK12Certificate input),
    Nonempty (ExactPreQ16K13StageOneFoldFailure decoder input)}

/-- Width-29 failure on exactly the word retained by corrected K1.3. -/
def exactPreQ16K14Width29Event
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (_k12 : ExactPrefixK12Certificate input)
      (k13 : ExactPreQ16K13StageCertificate decoder input),
    Width29DecompositionFailure decoder k13.words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule}

/-- K1.2 for the corrected package is the same exact prefix classifier already
bounded by the 208-bit two-tree theorem. -/
theorem preQ16_operational_k12_error_subset_exact_classified_event
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
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (environment : ExactPreQ16OperationalStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (source : ExactTag73K12SourceObligations transitionFuel configuration
      projection fixedInstance) :
    k12TwoTreeMerkle208ErrorEvent
        (exactTag73PreQ16OperationalStages transitionFuel configuration
          projection fixedInstance decoder decoderBinding basis rc poseidon
          transitionRoom programmedCover initialEncoderExact environment) ⊆
      exactPrefixK12ClassifiedErrorEvent transitionFuel configuration projection
        fixedInstance := by
  intro sample member
  rcases member with ⟨input, error⟩
  exact ⟨input, source.openingsAccepted sample input,
    source.suppliedCovered sample input, error⟩

/-- Complete deterministic cover for the narrow corrected K1.3 event. -/
theorem preQ16_operational_k13_error_subset_named_events
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
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (environment : ExactPreQ16OperationalStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) :
    k13CircleListDecodeErrorEvent
        (exactTag73PreQ16OperationalStages transitionFuel configuration
          projection fixedInstance decoder decoderBinding basis rc poseidon
          transitionRoom programmedCover initialEncoderExact environment) ⊆
      ((((exactPreQ16K13JointTrialUnion transitionFuel configuration projection
              fixedInstance decoder ∪
            exactPreQ16K13OneFoldEvent transitionFuel configuration projection
              fixedInstance decoder) ∪
          exactTag73K13JointQueryBatchCollisionEvent transitionFuel configuration
            projection fixedInstance decoder source) ∪
        exactTag73K13LaterRelationAlphaEvent transitionFuel configuration
          projection fixedInstance decoder source) ∪
      exactK13PreQ16LateTargetEvent transitionFuel configuration projection
        fixedInstance) := by
  intro sample member
  rcases member with ⟨input, k12, error⟩
  cases error.some with
  | idealRejected rejected =>
      rcases ideal_rejected_exposes_joint_or_later_relation_collision source
          rejected with joint | later
      · exact Or.inl (Or.inl (Or.inr ⟨input, k12, joint⟩))
      · rcases later with ⟨round, positive, repair⟩
        exact Or.inl (Or.inr ⟨input, k12, round, positive, repair⟩)
  | @q16 trial witness =>
      exact Or.inl (Or.inl (Or.inl (Or.inl
        (Set.mem_iUnion_of_mem trial ⟨witness⟩))))
  | oneFold failure =>
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨input, k12, ⟨failure⟩⟩)))
  | lateTarget late =>
      exact Or.inr late
  | collision collision =>
      exact False.elim (k12.noCollision collision)

/-- The corrected K1.4 error is exactly its pre-q16 width-29 event. -/
theorem preQ16_operational_k14_error_subset_width29
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
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (environment : ExactPreQ16OperationalStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) :
    k14CoherentChainErrorEvent
        (exactTag73PreQ16OperationalStages transitionFuel configuration
          projection fixedInstance decoder decoderBinding basis rc poseidon
          transitionRoom programmedCover initialEncoderExact environment) ⊆
      exactPreQ16K14Width29Event transitionFuel configuration projection
        fixedInstance decoder := by
  intro sample member
  rcases member with ⟨input, k12, k13, error⟩
  rcases error.some with ⟨parsed⟩
  cases parsed with
  | width29 failure => exact ⟨input, k12, k13, failure⟩

#print axioms preQ16_operational_k12_error_subset_exact_classified_event
#print axioms preQ16_operational_k13_error_subset_named_events
#print axioms preQ16_operational_k14_error_subset_width29

end

end AspisK1.V7Tag73PreQ16OperationalStageEvents
