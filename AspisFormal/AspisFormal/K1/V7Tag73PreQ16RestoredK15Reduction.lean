import AspisFormal.K1.V7Tag73ExactCausalK15Reduction
import AspisFormal.K1.V7Tag73PreQ16RestoredK15Context
import AspisFormal.K1.V7Tag73PreQ16RestoredK15Gamma

/-!
# Causal K1.5 reduction on the corrected pre-q16 extraction

The raw thirteen-way semantic failure is reduced to a restored coherent chain,
one fixed-family event, or the single constrained gamma event.  The generic
point-compatible kernel theorem keeps the corrected proof compact.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73PreQ16RestoredK15Reduction

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCausalK15Reduction
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73OperationalK15Classifier
open AspisK1.V7Tag73OperationalRelationSourceFacts
open AspisK1.V7Tag73PreQ16OperationalK15Semantic
open AspisK1.V7Tag73PreQ16OperationalK15Stage
open AspisK1.V7Tag73PreQ16OperationalRelationSourceFacts
open AspisK1.V7Tag73PreQ16RestoredK15Context
open AspisK1.V7Tag73PreQ16RestoredK15Gamma
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedTupleSemanticSecurity
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7K15FixedFamilyCausalCover
open AspisPool.V7PointClaimBatchBinding
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar

noncomputable section

/-- First, cheap half of the exact causal reduction.  It deliberately stops at
the causal predecessor bundle so the constrained-gamma proof remains behind
its own small opaque theorem boundary. -/
theorem exact_preQ16_operational_k15_failure_reduces_raw
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
      fixedInstance decoder decoderBinding)
    (failure : ExactPreQ16OperationalK15Failure
      (context.material environment.operational)) :
    HasAcceptedRestoredPointCompatibleK14 decoder context.k13.words
        (context.run environment.operational).point
        (context.fields environment.operational).pointClaim
        (environment.family context) ∨
      context.fixedFailure environment ∨
        ExactPreQ16GammaPredecessors environment context := by
  classical
  let material := context.material environment.operational
  let fields := context.fields environment.operational
  let transcript := context.run environment.operational
  let compact := operationalCompactEvidence context.input material.data.decoded
    material.data.fixedDecode
  have fixedMember : context.k14.parsed.extraction.components ∈
      fixedWidth29TupleList decoder
        (extractedWidth29InitialWords context.k13.words) :=
    coherentTraceExtraction_components_mem_fixedWidth29TupleList
      material.source.initialEncoderEq context.k14.parsed.extraction
  rcases failure.evidence with ⟨kind, holds, predecessorClear⟩
  apply failureKind_elim_causal basis rc fixedInstance.statement fields
    transcript compact context.k14.parsed.extraction
    (exactOperationalChallenge context.input .lambda)
    (exactOperationalChallenge context.input .chi)
    (exactOperationalChallenge context.input .theta)
    (fun coordinate ↦ exactOperationalChallenge context.input
      (.zerocheckPoint coordinate))
    (exactOperationalChallenge context.input .mu) material.data.helper
    material.data.mask material.exactHonest
    (exactOperationalChallenge context.input .kappa) material.data.execution
    fixedMember (environment.terminal context) (environment.sumcheck context)
    (environment.terminalExact context fixedMember)
    (environment.sumcheckCausal context fixedMember) kind
  · intro fixed
    exact Or.inr (Or.inl fixed)
  · intro kindIsGamma _gammaCollision
    obtain ⟨noOodEvent, noAlphaEvent, noKappaEvent⟩ :=
      predecessorClear kindIsGamma
    have noOod :
        ¬ material.data.execution.discrepancyTrace.MixCancellation 0 := by
      exact noOodEvent
    have noAlpha : ∀ round : Fin 4,
        ¬ material.data.execution.discrepancyTrace.AlphaRepair round := by
      intro round repair
      exact noAlphaEvent ⟨round, repair⟩
    have noKappa : ¬ KappaPointRowCollision fields context.k14.parsed.extraction
        transcript.point (exactOperationalChallenge context.input .kappa) := by
      exact noKappaEvent
    exact Or.inr (Or.inr ⟨noOod, noAlpha, noKappa⟩)
  · exact holds

#print axioms exact_preQ16_operational_k15_failure_reduces_raw

end

end AspisK1.V7Tag73PreQ16RestoredK15Reduction
