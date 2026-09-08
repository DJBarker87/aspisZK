import AspisFormal.K1.V7Tag73PreQ16RestoredStageAssembly
import AspisFormal.K1.V7Tag73PreQ16RestoredK15Reduction
import AspisFormal.K1.V7Tag73K15ExactMeasureLedger

/-! # Exact events for restoration-aware corrected pre-q16 K1.5 -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16RestoredK15Events

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisK1.V7Tag73PreQ16OperationalK15Stage
open AspisK1.V7Tag73PreQ16OperationalK15Semantic
open AspisK1.V7Tag73PreQ16RestoredK15Context
open AspisK1.V7Tag73PreQ16RestoredK15Gamma
open AspisK1.V7Tag73PreQ16RestoredK15Reduction
open AspisK1.V7Tag73PreQ16RestoredStageAssembly
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedC1CopyCollisionSecurity
open AspisPool.V7FixedTupleSemanticSecurity
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7K15FixedFamilyCausalCover
open AspisPool.V7PointClaimBatchBinding
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Literal predicate for each of the eight fixed K1.5 categories, indexed by
the corrected chronological words and coherent extraction. -/
def exactPreQ16FixedK15CategoryHolds
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
    (context : ExactPreQ16K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding) : FixedK15Category → Prop
  | .semantic =>
      FixedWidth29SemanticFailure decoder
        (extractedWidth29InitialWords context.k13.words)
        (environment.terminal context) (environment.sumcheck context)
        (exactOperationalChallenge context.input .theta)
        (fun coordinate ↦ exactOperationalChallenge context.input
          (.zerocheckPoint coordinate))
        (context.run environment.operational).point
        (exactOperationalChallenge context.input .mu)
  | .copyLambda => ∃ candidate : FixedC1TupleCandidate decoder
      (c1Received context.k13.words),
      CopyTupleCompressionCollision
        (fixedC1CopySourceFamily decoder (c1Received context.k13.words)
          candidate).registry
        (exactOperationalChallenge context.input .lambda)
  | .copyChi => ∃ candidate : FixedC1TupleCandidate decoder
      (c1Received context.k13.words),
      DeployedCopyActivePole
          (fixedC1CopySourceFamily decoder (c1Received context.k13.words)
            candidate).registry
          (exactOperationalChallenge context.input .lambda)
          (exactOperationalChallenge context.input .chi) ∨
        CopyChiCollision
          (fixedC1CopySourceFamily decoder (c1Received context.k13.words)
            candidate).registry
          (exactOperationalChallenge context.input .lambda)
          (exactOperationalChallenge context.input .chi)
  | .muZero => exactOperationalChallenge context.input .mu = 0
  | .inactiveChi => DeployedCopyInactiveSlotCollision
      (exactOperationalChallenge context.input .chi)
  | .oodMix =>
      (context.material environment.operational).data.execution.discrepancyTrace
        |>.MixCancellation 0
  | .relationAlpha => ∃ round : Fin 4,
      (context.material environment.operational).data.execution.discrepancyTrace
        |>.AlphaRepair round
  | .kappaPointRow => KappaPointRowCollision
      (context.fields environment.operational) context.k14.parsed.extraction
      (context.run environment.operational).point
      (exactOperationalChallenge context.input .kappa)

/-- Eight fixed events on the exact compiler sample space. -/
def exactPreQ16RestoredFixedK15Events
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
    FixedK15Events (ExactCompilerSample HiddenTape parameters) where
  event category := {sample | ∃ context : ExactPreQ16K15Context transitionFuel
    configuration projection fixedInstance decoder decoderBinding,
    context.sample = sample ∧
      exactPreQ16FixedK15CategoryHolds environment context category}

/-- Exact residual returned after both extraction routes and fixed failures have
been excluded. -/
def exactPreQ16RestoredK15ResidualEvent
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
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ context : ExactPreQ16K15Context transitionFuel configuration
      projection fixedInstance decoder decoderBinding,
    context.sample = sample ∧
      Nonempty (ExactPreQ16OperationalK15Failure
        (context.material environment.operational)) ∧
      ¬ context.fixedFailure environment ∧
      ¬ HasAcceptedRestoredPointCompatibleK14 decoder context.k13.words
        (context.run environment.operational).point
        (context.fields environment.operational).pointClaim
        (environment.family context)}

/-- Every returned K1.5 error is fixed-family or the exact residual. -/
theorem exact_preQ16_restored_k15_error_event_subset_fixed_union_residual
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
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (stageEnvironment : ExactPreQ16RestoredStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) :
    k15SpendWitnessErrorEvent
        (exactTag73PreQ16RestoredStages transitionFuel configuration projection
          fixedInstance decoder decoderBinding basis rc poseidon transitionRoom
          programmedCover initialEncoderExact stageEnvironment) ⊆
      (exactPreQ16RestoredFixedK15Events stageEnvironment.restoredK15).failure ∪
        exactPreQ16RestoredK15ResidualEvent stageEnvironment.restoredK15 := by
  intro sample member
  rcases member with ⟨input, k12, k13, k14, ⟨failure⟩⟩
  let context : ExactPreQ16K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding := ⟨sample, input, k12, k13, k14⟩
  rcases failure.evidence with fixed | residual
  · apply Or.inl
    rcases fixed with semantic | copyLambda | copyChi | muZero | inactiveChi |
        oodMix | relationAlpha | kappaPointRow
    · exact Set.mem_iUnion_of_mem .semantic
        ⟨context, rfl, by simpa only [context,
          exactPreQ16FixedK15CategoryHolds] using semantic⟩
    · exact Set.mem_iUnion_of_mem .copyLambda
        ⟨context, rfl, by simpa only [context,
          exactPreQ16FixedK15CategoryHolds] using copyLambda⟩
    · exact Set.mem_iUnion_of_mem .copyChi
        ⟨context, rfl, by simpa only [context,
          exactPreQ16FixedK15CategoryHolds] using copyChi⟩
    · exact Set.mem_iUnion_of_mem .muZero
        ⟨context, rfl, by simpa only [context,
          exactPreQ16FixedK15CategoryHolds] using muZero⟩
    · exact Set.mem_iUnion_of_mem .inactiveChi
        ⟨context, rfl, by simpa only [context,
          exactPreQ16FixedK15CategoryHolds] using inactiveChi⟩
    · exact Set.mem_iUnion_of_mem .oodMix
        ⟨context, rfl, by simpa only [context,
          exactPreQ16FixedK15CategoryHolds] using oodMix⟩
    · exact Set.mem_iUnion_of_mem .relationAlpha
        ⟨context, rfl, by simpa only [context,
          exactPreQ16FixedK15CategoryHolds] using relationAlpha⟩
    · exact Set.mem_iUnion_of_mem .kappaPointRow
        ⟨context, rfl, by simpa only [context,
          exactPreQ16FixedK15CategoryHolds] using kappaPointRow⟩
  · exact Or.inr ⟨context, rfl, residual⟩

#print axioms exact_preQ16_restored_k15_error_event_subset_fixed_union_residual

end

end AspisK1.V7Tag73PreQ16RestoredK15Events
