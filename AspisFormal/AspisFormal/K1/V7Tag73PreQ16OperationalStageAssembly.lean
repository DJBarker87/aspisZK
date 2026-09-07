import AspisFormal.K1.V7Tag73ExactFixedK16Closure
import AspisFormal.K1.V7Tag73PreQ16OperationalK15Classifier

/-!
# Corrected pre-q16 K1.2--K1.5 stage assembly

This installs the chronological pre-q16 K1.3 certificate, its dependent K1.4
certificate, and the operational K1.5 client handoff in the exact generic
K1.6 stage interface.  Source data is indexed by the literal scheduler input;
no stage may substitute a different proof, transcript, or Merkle word.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16OperationalStageAssembly

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16QueryHandoff
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73PreQ16OperationalK15Classifier
open AspisK1.V7Tag73PreQ16OperationalK15Semantic
open AspisK1.V7Tag73PreQ16OperationalK15Stage
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7MerkleQueryExtractor
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- Exact source facts consumed before the corrected K1.3 classifier.  The
canonical fixed-field decode is retained so its equality with K1.5's decode
can be proved rather than assumed. -/
structure ExactPreQ16OperationalK13Source
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type where
  decoded : Fin 641 → QM31Exact
  fixedDecode : FixedFieldDecodeExact
    (rawOfMessages (exactOperationalTape input).messages) decoded
  parsed : ExactParsedProofSourceBinding input decoded
  positions : ExactOpeningPositionsSourceBinding input
  frontierExact : ∀ schedule,
    (exactOperationalTape input).frontierNodes schedule =
      semanticFrontierNodes schedule.positions

/-- One source/restoration environment for all four dependent stages. -/
structure ExactPreQ16OperationalStageEnvironment
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
      deployedNullifier deployedNode) : Type where
  k13Source : ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample),
    ExactPreQ16OperationalK13Source input
  k15Environment : ExactPreQ16OperationalK15Environment transitionFuel
    configuration projection fixedInstance decoder decoderBinding basis rc
    poseidon

/-- Canonical decoding prevents the K1.3 and K1.5 source layers from assigning
different mathematical values to the same accepted raw bytes. -/
theorem ExactPreQ16OperationalStageEnvironment.k13Decoded_eq_k15Decoded
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
    (environment : ExactPreQ16OperationalStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (sample : ExactCompilerSample HiddenTape parameters)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (k13 : ExactPreQ16K13StageCertificate decoder input)
    (k14 : ExactPreQ16K14StageCertificate decoder decoderBinding input k13) :
    (environment.k13Source sample input).decoded =
      (environment.k15Environment.material sample input k12 k13 k14).data.decoded :=
  fixedFieldDecodeExact_unique (environment.k13Source sample input).fixedDecode
    (environment.k15Environment.material sample input k12 k13 k14).data.fixedDecode

/-- Narrow operational K1.3 classifier.  The older broad `ExactK13Error`
type contains branches that this chronological classifier never returns; using
that broad type in the proof-relevant event would nevertheless count every
inhabited branch.  This definition exposes exactly the actual outcomes:
successful pre-q16 extraction or one of `ExactPreQ16K13StageError`'s named
failures. -/
noncomputable def classifyPreQ16OperationalK13
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (decoded : Fin 641 → QM31Exact)
    (source : ExactParsedProofSourceBinding input decoded)
    (positions : ExactOpeningPositionsSourceBinding input)
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    ExactPreQ16K13StageCertificate decoder input ⊕
      ExactPreQ16K13StageError decoder input k12 := by
  classical
  by_cases accepts : IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries
  · exact classifyAcceptedInputThroughPreQ16Stage transitionRoom
      programmedCover initialEncoderExact input k12 decoded source positions
      frontierExact accepts
  · exact .inr (.idealRejected accepts)

/-- Corrected production-semantic stage package consumed by K1.6. -/
noncomputable def exactTag73PreQ16OperationalStages
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
    ProofRelevantK12ToK15Stages transitionFuel configuration fixedInstance
      (exactTag73SpendRelation (deployedOwner := deployedOwner)
        (deployedNote := deployedNote)
        (deployedNullifier := deployedNullifier)
        (deployedNode := deployedNode))
      (ExactFixedSchedulerK12ToK15Input transitionFuel configuration projection
        fixedInstance) where
  k12TwoTreeMerkle208Certificate := fun _sample input =>
    ExactPrefixK12Certificate input
  k12TwoTreeMerkle208Error := fun _sample input => ExactPrefixK12Error input
  classifyK12TwoTreeMerkle208 := fun _sample input => classifyExactPrefixK12 input
  k13CircleListDecodeCertificate := fun _sample input _k12 =>
    ExactPreQ16K13StageCertificate decoder input
  k13CircleListDecodeError := fun _sample input k12 =>
    ExactPreQ16K13StageError decoder input k12
  classifyK13CircleListDecode := fun sample input k12 =>
    let source := environment.k13Source sample input
    classifyPreQ16OperationalK13 transitionRoom programmedCover
      initialEncoderExact input k12 source.decoded source.parsed
      source.positions source.frontierExact
  k14CoherentChainCertificate := fun _sample input _k12 k13 =>
    ExactPreQ16K14StageCertificate decoder decoderBinding input k13
  k14CoherentChainError := fun _sample input _k12 k13 =>
    ExactPreQ16K14StageError decoder input k13
  classifyK14CoherentChain := fun _sample input _k12 k13 =>
    classifyPreQ16K14Stage decoder decoderBinding input k13
  k15SpendWitnessError := fun sample input k12 k13 k14 =>
    ExactPreQ16OperationalK15Failure
      (environment.k15Environment.material sample input k12 k13 k14)
  classifyK15SpendWitness := fun sample input k12 k13 k14 =>
    classifyPreQ16OperationalK15 transitionFuel configuration projection
      fixedInstance decoder decoderBinding basis rc poseidon
      environment.k15Environment sample input k12 k13 k14

#print axioms ExactPreQ16OperationalStageEnvironment.k13Decoded_eq_k15Decoded
#print axioms classifyPreQ16OperationalK13
#print axioms exactTag73PreQ16OperationalStages

end


end AspisK1.V7Tag73PreQ16OperationalStageAssembly
