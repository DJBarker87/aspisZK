import AspisFormal.K1.V7Tag73PreQ16OperationalStageAssembly
import AspisFormal.K1.V7Tag73PreQ16RestoredK15Classifier

/-! # Corrected pre-q16 stages with restoration-aware K1.5 -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16RestoredStageAssembly

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73PreQ16OperationalStageAssembly
open AspisK1.V7Tag73PreQ16RestoredK15Classifier
open AspisK1.V7Tag73PreQ16RestoredK15Context
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- The already-proved chronological K1.2--K1.4 environment paired with the
restoration-aware K1.5 environment.  Equality of their operational material
provider is explicit, preventing the two layers from selecting different
decoded proof data. -/
structure ExactPreQ16RestoredStageEnvironment
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
  operationalStages : ExactPreQ16OperationalStageEnvironment transitionFuel
    configuration projection fixedInstance decoder decoderBinding basis rc
    poseidon
  restoredK15 : ExactPreQ16RestoredK15Environment transitionFuel configuration
    projection fixedInstance decoder decoderBinding basis rc poseidon
  operationalExact : restoredK15.operational =
    operationalStages.k15Environment

/-- The corrected K1.2--K1.4 classifiers with restoration-aware K1.5. -/
noncomputable def exactTag73PreQ16RestoredStages
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
    (environment : ExactPreQ16RestoredStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) :
    ProofRelevantK12ToK15Stages transitionFuel configuration fixedInstance
      (exactTag73SpendRelation (deployedOwner := deployedOwner)
        (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
        (deployedNode := deployedNode))
      (ExactFixedSchedulerK12ToK15Input transitionFuel configuration projection
        fixedInstance) := by
  let upstream := exactTag73PreQ16OperationalStages transitionFuel configuration
    projection fixedInstance decoder decoderBinding basis rc poseidon
    transitionRoom programmedCover initialEncoderExact
    environment.operationalStages
  exact
    { k12TwoTreeMerkle208Certificate := upstream.k12TwoTreeMerkle208Certificate
      k12TwoTreeMerkle208Error := upstream.k12TwoTreeMerkle208Error
      classifyK12TwoTreeMerkle208 := upstream.classifyK12TwoTreeMerkle208
      k13CircleListDecodeCertificate := upstream.k13CircleListDecodeCertificate
      k13CircleListDecodeError := upstream.k13CircleListDecodeError
      classifyK13CircleListDecode := upstream.classifyK13CircleListDecode
      k14CoherentChainCertificate := upstream.k14CoherentChainCertificate
      k14CoherentChainError := upstream.k14CoherentChainError
      classifyK14CoherentChain := upstream.classifyK14CoherentChain
      k15SpendWitnessError := fun sample input k12 k13 k14 =>
        ExactPreQ16RestoredK15Failure environment.restoredK15
          ⟨sample, input, k12, k13, k14⟩
      classifyK15SpendWitness := fun sample input k12 k13 k14 =>
        classifyPreQ16RestoredK15 transitionFuel configuration projection
          fixedInstance decoder decoderBinding basis rc poseidon
          environment.restoredK15 sample input k12 k13 k14 }

#print axioms exactTag73PreQ16RestoredStages

end

end AspisK1.V7Tag73PreQ16RestoredStageAssembly
