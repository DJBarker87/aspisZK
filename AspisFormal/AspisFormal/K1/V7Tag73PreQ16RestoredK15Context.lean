import AspisFormal.K1.V7Tag73PreQ16OperationalK15Classifier
import AspisFormal.K1.V7Tag73RestoredPointCompatibleK14
import AspisFormal.Pool.V7K15FixedFamilyCausalCover

/-!
# Restoration context for corrected pre-q16 K1.5

This file contains only dependent data.  It fixes the restored-chain family,
semantic plans, and client handoff to the exact chronological word and
coherent extraction returned by corrected K1.3/K1.4.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16RestoredK15Context

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73OperationalK15Classifier
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73PreQ16OperationalK15Classifier
open AspisK1.V7Tag73PreQ16OperationalK15Semantic
open AspisK1.V7Tag73PreQ16OperationalK15Stage
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedTupleSemanticSecurity
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7K15FixedFamilyCausalCover
open AspisPool.V7PointClaimBatchBinding
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar

noncomputable section

/-- Complete corrected dependent K1.5 index. -/
structure ExactPreQ16K15Context
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
    (decoderBinding : InitialProjectionBinding decoder) where
  sample : ExactCompilerSample HiddenTape parameters
  input : ExactK12OperationalInput transitionFuel configuration projection
    fixedInstance sample
  k12 : ExactPrefixK12Certificate input
  k13 : ExactPreQ16K13StageCertificate decoder input
  k14 : ExactPreQ16K14StageCertificate decoder decoderBinding input k13

def ExactPreQ16K15Context.material
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
    (context : ExactPreQ16K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding)
    (operational : ExactPreQ16OperationalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) :=
  operational.material context.sample context.input context.k12 context.k13
    context.k14

def ExactPreQ16K15Context.fields
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
    (context : ExactPreQ16K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding)
    (operational : ExactPreQ16OperationalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) : FixedFieldView QM31Exact :=
  operationalFixedFields (context.material operational).data.decoded

def ExactPreQ16K15Context.run
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
    (context : ExactPreQ16K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding)
    (operational : ExactPreQ16OperationalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) :=
  operationalAcceptedRun context.input (context.material operational).data.decoded
    (context.material operational).data.fixedDecode

/-- Client evidence for a valid witness recovered on a restored branch. -/
structure ExactPreQ16RestoredClientResult
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
    (context : ExactPreQ16K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest} : Type where
  witness : DecodedSpendWitness
  relationValid : exactTag73SpendRelation (deployedOwner := deployedOwner)
    (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
    (deployedNode := deployedNode) fixedInstance witness
  extractor : ExactPlainRomWitnessExtractor V5PublicStatement
    Tag73K12ParsedProof Payload DecodedSpendWitness
  clientReturned : context.input.package.root.full.clientRun.halt =
    .returned extractor
  extractorReturned : extractor
    context.input.package.root.full.clientRun.accumulator = some witness

/-- Exact restoration/source provider for corrected pre-q16 K1.5. -/
structure ExactPreQ16RestoredK15Environment
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
  operational : ExactPreQ16OperationalK15Environment transitionFuel
    configuration projection fixedInstance decoder decoderBinding basis rc
    poseidon
  family : (context : ExactPreQ16K15Context transitionFuel configuration
      projection fixedInstance decoder decoderBinding) →
    RestoredSelectedChainFamily decoder context.k13.words
  familyAvailable : ∀ context,
    (family context).available (exactK13ParsedProof context.input).gamma
  familySelected : ∀ context,
    (family context).selected (exactK13ParsedProof context.input).gamma =
      context.k14.parsed.extraction.combined
  terminal : ∀ context : ExactPreQ16K15Context transitionFuel configuration
      projection fixedInstance decoder decoderBinding,
    FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords context.k13.words) →
        FixedTerminalAlgebraPlan QM31Exact
  sumcheck : ∀ context : ExactPreQ16K15Context transitionFuel configuration
      projection fixedInstance decoder decoderBinding,
    FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords context.k13.words) →
        AdaptiveDegree27MessagePlan QM31Exact
  terminalExact : ∀
      (context : ExactPreQ16K15Context transitionFuel configuration projection
        fixedInstance decoder decoderBinding)
      (member : context.k14.parsed.extraction.components ∈
        fixedWidth29TupleList decoder
          (extractedWidth29InitialWords context.k13.words)),
    terminal context
        (extractedFixedWidth29Candidate context.k14.parsed.extraction member) =
      extractedFixedTerminalPlan basis rc fixedInstance.statement
        context.k14.parsed.extraction
        (exactOperationalChallenge context.input .lambda)
        (exactOperationalChallenge context.input .chi)
        (context.material operational).data.helper
  sumcheckCausal : ∀
      (context : ExactPreQ16K15Context transitionFuel configuration projection
        fixedInstance decoder decoderBinding)
      (member : context.k14.parsed.extraction.components ∈
        fixedWidth29TupleList decoder
          (extractedWidth29InitialWords context.k13.words)),
    WireUsesAdaptiveDegree27Plan
      (acceptedProductionWireOfCompact (context.fields operational)
        (context.run operational)
        (operationalCompactEvidence context.input
          (context.material operational).data.decoded
          (context.material operational).data.fixedDecode))
      (context.material operational).exactHonest
      (sumcheck context
        (extractedFixedWidth29Candidate context.k14.parsed.extraction member))
  pointCompatibleResult : ∀
      (context : ExactPreQ16K15Context transitionFuel configuration projection
        fixedInstance decoder decoderBinding),
    (¬ FixedFamilyK15Failure (terminal context) (sumcheck context)
        (context.fields operational) context.k14.parsed.extraction
        (fun coordinate ↦ exactOperationalChallenge context.input
          (.zerocheckPoint coordinate))
        (context.run operational).point
        (exactOperationalChallenge context.input .lambda)
        (exactOperationalChallenge context.input .chi)
        (exactOperationalChallenge context.input .theta)
        (exactOperationalChallenge context.input .mu)
        (exactOperationalChallenge context.input .kappa)
        (context.material operational).data.execution) →
      HasAcceptedRestoredPointCompatibleK14 decoder context.k13.words
        (context.run operational).point
        (context.fields operational).pointClaim (family context) →
      Nonempty (ExactPreQ16RestoredClientResult context
        (deployedOwner := deployedOwner) (deployedNote := deployedNote)
        (deployedNullifier := deployedNullifier)
        (deployedNode := deployedNode))

/-- Fixed-family proposition at one corrected context. -/
def ExactPreQ16K15Context.fixedFailure
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
    (context : ExactPreQ16K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding)
    (environment : ExactPreQ16RestoredK15Environment transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon) : Prop :=
  FixedFamilyK15Failure (environment.terminal context)
    (environment.sumcheck context) (context.fields environment.operational)
    context.k14.parsed.extraction
    (fun coordinate ↦ exactOperationalChallenge context.input
      (.zerocheckPoint coordinate))
    (context.run environment.operational).point
    (exactOperationalChallenge context.input .lambda)
    (exactOperationalChallenge context.input .chi)
    (exactOperationalChallenge context.input .theta)
    (exactOperationalChallenge context.input .mu)
    (exactOperationalChallenge context.input .kappa)
    (context.material environment.operational).data.execution

/-- Only the fixed-family or constrained-restoration branches remain errors. -/
structure ExactPreQ16RestoredK15Failure
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
      fixedInstance decoder decoderBinding) : Type where
  evidence : context.fixedFailure environment ∨
    (Nonempty (ExactPreQ16OperationalK15Failure
        (context.material environment.operational)) ∧
      ¬ context.fixedFailure environment ∧
      ¬ HasAcceptedRestoredPointCompatibleK14 decoder context.k13.words
        (context.run environment.operational).point
        (context.fields environment.operational).pointClaim
        (environment.family context))

/-- The three causal facts retained when the ordered K1.5 classifier reaches
the final gamma/point-claim branch.  Bundling them prevents repeated dependent
normalization when the gamma lemma is consumed by event code. -/
structure ExactPreQ16GammaPredecessors
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
      fixedInstance decoder decoderBinding) : Prop where
  noOod : ¬ (context.material environment.operational).data.execution.discrepancyTrace.MixCancellation 0
  noAlpha : ∀ round : Fin 4,
    ¬ (context.material environment.operational).data.execution.discrepancyTrace.AlphaRepair round
  noKappa : ¬ KappaPointRowCollision
    (context.fields environment.operational) context.k14.parsed.extraction
    (context.run environment.operational).point
    (exactOperationalChallenge context.input .kappa)

#print axioms ExactPreQ16K15Context.fixedFailure
#print axioms ExactPreQ16RestoredK15Failure
#print axioms ExactPreQ16GammaPredecessors

end

end AspisK1.V7Tag73PreQ16RestoredK15Context
