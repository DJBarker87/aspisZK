import AspisFormal.K1.V7Tag73GammaRestoredOperationalK14Stage
import AspisFormal.K1.V7Tag73ExactFixedK16Closure

/-!
# Correctly scoped gamma-restored K1.2--K1.5 stages

The generic K1.6 interface requires a dependent K1.3 then K1.4 selection.
This package chooses only a K1.3 certificate whose node was created by the
canonical block-zero root-gamma restoration request.  K1.4 is therefore
definitionally about the same child whose fresh gamma law is bounded by
`V7Tag73GammaRestoredK14Probability`.

Failure to obtain such a K1.3 certificate remains an explicit K1.3 event.  It
is not hidden inside K1.4 and is not replaced by the weaker fact that some
unrelated restoration node classified successfully.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73GammaRestoredOperationalStages

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73GammaRestoredOperationalK14Stage
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Exact failure of the scoped K1.3 selection. -/
structure ExactGammaRestoredOperationalK13Error
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type where
  noCertificate : ¬ Nonempty
    (ExactGammaRestoredOperationalK13Certificate decoder input)

/-- Total selection of the canonical gamma-restored K1.3 child. -/
noncomputable def classifyExactGammaRestoredOperationalK13
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ExactGammaRestoredOperationalK13Certificate decoder input ⊕
      ExactGammaRestoredOperationalK13Error decoder input := by
  classical
  by_cases available : Nonempty
      (ExactGammaRestoredOperationalK13Certificate decoder input)
  · exact .inl (Classical.choice available)
  · exact .inr ⟨available⟩

/-- Final source/client handoff for the same scoped K1.3/K1.4 child. -/
structure ExactGammaRestoredOperationalK15Classifier
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder) where
  error :
    (sample : ExactCompilerSample HiddenTape parameters) →
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample) →
      (k13 : ExactGammaRestoredOperationalK13Certificate decoder input) →
      ExactGammaRestoredOperationalK14Certificate decoder binding input k13 →
        Type
  classify :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k13 : ExactGammaRestoredOperationalK13Certificate decoder input)
      (k14 : ExactGammaRestoredOperationalK14Certificate decoder binding input
        k13),
      ExactFixedClientExtractionCertificate transitionFuel configuration
          fixedInstance relation sample ⊕
        error sample input k13 k14

/-- Stage package whose dependent indices make cross-node K1.4 substitution
impossible. -/
noncomputable def exactTag73GammaRestoredOperationalStages
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (k15 : ExactGammaRestoredOperationalK15Classifier transitionFuel
      configuration projection fixedInstance relation decoder binding) :
    ProofRelevantK12ToK15Stages transitionFuel configuration fixedInstance
      relation
        (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
          projection fixedInstance) where
  k12TwoTreeMerkle208Certificate := fun _sample _input => Unit
  k12TwoTreeMerkle208Error := fun _sample _input => Empty
  classifyK12TwoTreeMerkle208 := fun _sample _input => .inl ()
  k13CircleListDecodeCertificate := fun _sample input _unit =>
    ExactGammaRestoredOperationalK13Certificate decoder input
  k13CircleListDecodeError := fun _sample input _unit =>
    ExactGammaRestoredOperationalK13Error decoder input
  classifyK13CircleListDecode := fun _sample input _unit =>
    classifyExactGammaRestoredOperationalK13 decoder input
  k14CoherentChainCertificate := fun _sample input _unit k13 =>
    ExactGammaRestoredOperationalK14Certificate decoder binding input k13
  k14CoherentChainError := fun _sample input _unit k13 =>
    ExactGammaRestoredOperationalK14Error decoder input k13
  classifyK14CoherentChain := fun _sample input _unit k13 =>
    classifyExactGammaRestoredOperationalK14 decoder binding input k13
  k15SpendWitnessError := fun sample input _unit k13 k14 =>
    k15.error sample input k13 k14
  classifyK15SpendWitness := fun sample input _unit k13 k14 =>
    k15.classify sample input k13 k14

/-- Literal absence/failure event for the scoped K1.3 child. -/
def exactTag73GammaRestoredOperationalK13FailureEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ input : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance sample,
    Nonempty (ExactGammaRestoredOperationalK13Error decoder input)}

/-- Literal final-handoff failure event for the scoped child. -/
def exactTag73GammaRestoredOperationalK15FailureEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    (k15 : ExactGammaRestoredOperationalK15Classifier transitionFuel
      configuration projection fixedInstance relation decoder binding) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k13 : ExactGammaRestoredOperationalK13Certificate decoder input)
      (k14 : ExactGammaRestoredOperationalK14Certificate decoder binding input
        k13),
    Nonempty (k15.error sample input k13 k14)}

theorem exact_gamma_restored_stages_k12_error_event_eq_empty
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    (k15 : ExactGammaRestoredOperationalK15Classifier transitionFuel
      configuration projection fixedInstance relation decoder binding) :
    k12TwoTreeMerkle208ErrorEvent
        (exactTag73GammaRestoredOperationalStages transitionFuel configuration
          projection fixedInstance relation decoder binding k15) = ∅ := by
  ext sample
  constructor
  · rintro ⟨_input, ⟨failure⟩⟩
    exact failure.elim
  · simp

theorem exact_gamma_restored_stages_k13_error_event_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    (k15 : ExactGammaRestoredOperationalK15Classifier transitionFuel
      configuration projection fixedInstance relation decoder binding) :
    k13CircleListDecodeErrorEvent
        (exactTag73GammaRestoredOperationalStages transitionFuel configuration
          projection fixedInstance relation decoder binding k15) =
      exactTag73GammaRestoredOperationalK13FailureEvent transitionFuel
        configuration projection fixedInstance decoder := by
  ext sample
  constructor
  · rintro ⟨input, unitValue, failure⟩
    cases unitValue
    exact ⟨input, failure⟩
  · rintro ⟨input, failure⟩
    exact ⟨input, (), failure⟩

theorem exact_gamma_restored_stages_k14_error_event_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    (k15 : ExactGammaRestoredOperationalK15Classifier transitionFuel
      configuration projection fixedInstance relation decoder binding) :
    k14CoherentChainErrorEvent
        (exactTag73GammaRestoredOperationalStages transitionFuel configuration
          projection fixedInstance relation decoder binding k15) =
      exactTag73GammaRestoredOperationalK14FailureEvent transitionFuel
        configuration projection fixedInstance decoder := by
  ext sample
  constructor
  · rintro ⟨input, unitValue, k13, failure⟩
    cases unitValue
    exact ⟨input, k13, failure⟩
  · rintro ⟨input, k13, failure⟩
    exact ⟨input, (), k13, failure⟩

theorem exact_gamma_restored_stages_k15_error_event_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    (k15 : ExactGammaRestoredOperationalK15Classifier transitionFuel
      configuration projection fixedInstance relation decoder binding) :
    k15SpendWitnessErrorEvent
        (exactTag73GammaRestoredOperationalStages transitionFuel configuration
          projection fixedInstance relation decoder binding k15) =
      exactTag73GammaRestoredOperationalK15FailureEvent k15 := by
  ext sample
  constructor
  · rintro ⟨input, unitValue, k13, k14, failure⟩
    cases unitValue
    exact ⟨input, k13, k14, failure⟩
  · rintro ⟨input, k13, k14, failure⟩
    exact ⟨input, (), k13, k14, failure⟩

#print axioms classifyExactGammaRestoredOperationalK13
#print axioms exactTag73GammaRestoredOperationalStages
#print axioms exact_gamma_restored_stages_k12_error_event_eq_empty
#print axioms exact_gamma_restored_stages_k13_error_event_eq
#print axioms exact_gamma_restored_stages_k14_error_event_eq
#print axioms exact_gamma_restored_stages_k15_error_event_eq

end
end AspisK1.V7Tag73GammaRestoredOperationalStages
