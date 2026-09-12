import AspisFormal.K1.V7Tag73GammaRestoredK14ByteTraceAlignment
import AspisFormal.K1.V7Tag73RestoredK12CanonicalWordCongruence

/-!
# Functional pre-gamma word selection from byte-level trace facts

The production bridge must not be allowed to choose an arbitrary word-valued
function after seeing gamma.  This leaf instead asks for the natural source
property: any two relevant executions in the same non-gamma coordinate fibre
have the same authenticated K1.2 word.  Lean chooses the fibre's word when a
relevant execution exists and uses a harmless default otherwise.

Together with literal bounded-decoder replay, that pairwise invariant builds
the complete byte-level K1.4 source consumed by the probability theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73GammaRestoredK14ByteFunctional

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactRestoredGammaFullRouting
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaRestoredK14ByteTraceAlignment
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredK12CanonicalWordCongruence
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleUntypedErasureStability
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- One clean failing execution together with the literal bounded gamma
decoder replay, indexed by its non-gamma coordinate residual. -/
structure GammaRestoredK14ByteFibreWitness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (hidden : HiddenTape)
    (residual : ExactCompilerGammaPrefixResidual parameters) : Type where
  answers : FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length
  cleanMember : (hidden, answers) ∈ clean
  input : ExactK12OperationalInput transitionFuel configuration projection
    fixedInstance (hidden, answers)
  k13 : ExactGammaRestoredOperationalK13Certificate decoder input
  failure : Width29DecompositionFailure decoder
    k13.certificate.classified.k12.words
    (restoredOperationalK13View k13.certificate.data).gamma
    (restoredOperationalK13View k13.certificate.data).disclosedFinal
    (restoredOperationalK13View k13.certificate.data).schedule
  decoded : OrdinaryPrefixDecode
  run : runGammaPrefix
      (exactCompilerRestoredGammaCoordinates transitionFuel configuration hidden
        answers).2 = some decoded
  residualExact :
    (exactCompilerRestoredGammaCoordinates transitionFuel configuration hidden
      answers).1 = residual
  bytesExact : decoded.value = k13.certificate.data.gammaBytes

/-- Equality of the literal K1.2 hash view, roots, and ordered query source is
sufficient for word invariance.  Different supplied opening objects are
allowed: successful extraction against the same complete source is
functional.  This exact-source form is retained for low-level adapters; the
typed form below is the release-facing theorem. -/
theorem gamma_restored_k14_byte_fibre_words_eq_of_exact_k12_source
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    {hidden : HiddenTape}
    {residual : ExactCompilerGammaPrefixResidual parameters}
    (left right : GammaRestoredK14ByteFibreWitness transitionFuel configuration
      projection fixedInstance decoder clean hidden residual)
    (truncateExact : restoredNodeK12Truncate left.k13.certificate.node =
      restoredNodeK12Truncate right.k13.certificate.node)
    (rootsExact : restoredNodeK12Roots left.k13.certificate.node =
      restoredNodeK12Roots right.k13.certificate.node)
    (queriesExact : restoredNodeK12OrderedQueries left.k13.certificate.node =
      restoredNodeK12OrderedQueries right.k13.certificate.node) :
    left.k13.certificate.classified.k12.words =
      right.k13.certificate.classified.k12.words := by
  have rightRun :
      extractV7Words (restoredNodeK12Truncate left.k13.certificate.node)
          (restoredNodeK12Roots left.k13.certificate.node)
          (restoredNodeK12Openings right.k13.certificate.node)
          (restoredNodeK12OrderedQueries left.k13.certificate.node) =
        .words right.k13.certificate.classified.k12.words := by
    simpa only [truncateExact, rootsExact, queriesExact] using
      right.k13.certificate.classified.k12.extracted
  exact extract_v7_words_success_words_eq_of_same_source
    (restoredNodeK12Truncate left.k13.certificate.node)
    (restoredNodeK12Roots left.k13.certificate.node)
    (restoredNodeK12Openings left.k13.certificate.node)
    (restoredNodeK12Openings right.k13.certificate.node)
    (restoredNodeK12OrderedQueries left.k13.certificate.node)
    left.k13.certificate.classified.k12.words
    right.k13.certificate.classified.k12.words
    left.k13.certificate.classified.k12.extracted rightRun

/-- The release-facing word invariant needs only the typed Merkle portion of
the node-local oracle histories.  Transcript-only entries after gamma are
deliberately unconstrained. -/
theorem gamma_restored_k14_byte_fibre_words_eq_of_typed_k12_source
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    {hidden : HiddenTape}
    {residual : ExactCompilerGammaPrefixResidual parameters}
    (left right : GammaRestoredK14ByteFibreWitness transitionFuel configuration
      projection fixedInstance decoder clean hidden residual)
    (truncateAgree : ∀ input, parseTypedPreimage input ≠ none →
      restoredNodeK12Truncate left.k13.certificate.node input =
        restoredNodeK12Truncate right.k13.certificate.node input)
    (rootsExact : restoredNodeK12Roots left.k13.certificate.node =
      restoredNodeK12Roots right.k13.certificate.node)
    (typedQueriesExact :
      retainTypedMerkleQueries (deduplicateFirst
          (restoredNodeK12OrderedQueries left.k13.certificate.node)) =
        retainTypedMerkleQueries (deduplicateFirst
          (restoredNodeK12OrderedQueries right.k13.certificate.node))) :
    left.k13.certificate.classified.k12.words =
      right.k13.certificate.classified.k12.words :=
  restored_node_k12_certificate_words_eq_of_typed_hash_agreement
    left.k13.certificate.node right.k13.certificate.node
    left.k13.certificate.classified.k12
    right.k13.certificate.classified.k12 truncateAgree rootsExact
    typedQueriesExact

/-- Source-facing functional facts.  `sameWords` is a pairwise pre-gamma
invariance statement; it does not supply a post-gamma word function or a bad
challenge set. -/
structure ExactTag73GammaRestoredK14ByteFunctional
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  defaultWords : ExtractedWords
  defaultResponse : InitialMessage QM31Exact
  defaultDisclosedFinal : FinalMessage QM31Exact
  defaultSchedule : ExactSchedule
  defaultSelected : ExactCandidatePair
  decoderAt : ∀ (hidden : HiddenTape)
      (answers : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (_cleanMember : (hidden, answers) ∈ clean)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance (hidden, answers))
      (k13 : ExactGammaRestoredOperationalK13Certificate decoder input)
      (_failure : Width29DecompositionFailure decoder
        k13.certificate.classified.k12.words
        (restoredOperationalK13View k13.certificate.data).gamma
        (restoredOperationalK13View k13.certificate.data).disclosedFinal
        (restoredOperationalK13View k13.certificate.data).schedule),
    ∃ decoded : OrdinaryPrefixDecode,
      runGammaPrefix
          (exactCompilerRestoredGammaCoordinates transitionFuel configuration
            hidden answers).2 = some decoded ∧
        decoded.value = k13.certificate.data.gammaBytes
  sameWords : ∀ (hidden : HiddenTape)
      (residual : ExactCompilerGammaPrefixResidual parameters)
      (left right : GammaRestoredK14ByteFibreWitness transitionFuel
        configuration projection fixedInstance decoder clean hidden residual),
    left.k13.certificate.classified.k12.words =
      right.k13.certificate.classified.k12.words

/-- A source-facing form which exposes only the three Merkle facts needed to
derive `sameWords`.  In particular it does not identify complete prover or
verifier runtimes: an adversary may have queried the eventual gamma input
before the verifier reaches it, and later transcript traffic may differ
between points of the gamma fibre.

The retained-query equality is deliberately restricted to inputs accepted by
the typed Merkle grammar.  Transcript SHA inputs are erased before comparison. -/
structure ExactTag73GammaRestoredK14TypedMerkleFunctional
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  defaultWords : ExtractedWords
  defaultResponse : InitialMessage QM31Exact
  defaultDisclosedFinal : FinalMessage QM31Exact
  defaultSchedule : ExactSchedule
  defaultSelected : ExactCandidatePair
  decoderAt : ∀ (hidden : HiddenTape)
      (answers : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (_cleanMember : (hidden, answers) ∈ clean)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance (hidden, answers))
      (k13 : ExactGammaRestoredOperationalK13Certificate decoder input)
      (_failure : Width29DecompositionFailure decoder
        k13.certificate.classified.k12.words
        (restoredOperationalK13View k13.certificate.data).gamma
        (restoredOperationalK13View k13.certificate.data).disclosedFinal
        (restoredOperationalK13View k13.certificate.data).schedule),
    ∃ decoded : OrdinaryPrefixDecode,
      runGammaPrefix
          (exactCompilerRestoredGammaCoordinates transitionFuel configuration
            hidden answers).2 = some decoded ∧
        decoded.value = k13.certificate.data.gammaBytes
  typedHashAgree : ∀ (hidden : HiddenTape)
      (residual : ExactCompilerGammaPrefixResidual parameters)
      (left right : GammaRestoredK14ByteFibreWitness transitionFuel
        configuration projection fixedInstance decoder clean hidden residual)
      (input : RawHashInput),
    parseTypedPreimage input ≠ none →
      restoredNodeK12Truncate left.k13.certificate.node input =
        restoredNodeK12Truncate right.k13.certificate.node input
  rootsExact : ∀ (hidden : HiddenTape)
      (residual : ExactCompilerGammaPrefixResidual parameters)
      (left right : GammaRestoredK14ByteFibreWitness transitionFuel
        configuration projection fixedInstance decoder clean hidden residual),
    restoredNodeK12Roots left.k13.certificate.node =
      restoredNodeK12Roots right.k13.certificate.node
  typedQueriesExact : ∀ (hidden : HiddenTape)
      (residual : ExactCompilerGammaPrefixResidual parameters)
      (left right : GammaRestoredK14ByteFibreWitness transitionFuel
        configuration projection fixedInstance decoder clean hidden residual),
    retainTypedMerkleQueries (deduplicateFirst
        (restoredNodeK12OrderedQueries left.k13.certificate.node)) =
      retainTypedMerkleQueries (deduplicateFirst
        (restoredNodeK12OrderedQueries right.k13.certificate.node))

/-- Typed Merkle source facts imply the abstract pairwise word functional.
This is the sole place where complete-extraction functionality is used. -/
def ExactTag73GammaRestoredK14TypedMerkleFunctional.toByteFunctional
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    (source : ExactTag73GammaRestoredK14TypedMerkleFunctional transitionFuel
      configuration projection fixedInstance decoder clean) :
    ExactTag73GammaRestoredK14ByteFunctional transitionFuel configuration
      projection fixedInstance decoder clean where
  defaultWords := source.defaultWords
  defaultResponse := source.defaultResponse
  defaultDisclosedFinal := source.defaultDisclosedFinal
  defaultSchedule := source.defaultSchedule
  defaultSelected := source.defaultSelected
  decoderAt := source.decoderAt
  sameWords := by
    intro hidden residual left right
    exact gamma_restored_k14_byte_fibre_words_eq_of_typed_k12_source left right
      (source.typedHashAgree hidden residual left right)
      (source.rootsExact hidden residual left right)
      (source.typedQueriesExact hidden residual left right)

/-- Canonical word attached to one non-gamma fibre.  Existence and choice are
made before the probability theorem sees the gamma coordinate. -/
noncomputable def ExactTag73GammaRestoredK14ByteFunctional.fibreWords
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    (source : ExactTag73GammaRestoredK14ByteFunctional transitionFuel
      configuration projection fixedInstance decoder clean)
    (hidden : HiddenTape)
    (residual : ExactCompilerGammaPrefixResidual parameters) : ExtractedWords :=
  by
    classical
    exact
      if existsWitness : Nonempty (GammaRestoredK14ByteFibreWitness
          transitionFuel configuration projection fixedInstance decoder clean
            hidden residual) then
        (Classical.choice existsWitness).k13.certificate.classified.k12.words
      else
        source.defaultWords

/-- Pairwise word invariance and byte replay construct the pre-fixed source
used by restored-gamma K1.4. -/
noncomputable def ExactTag73GammaRestoredK14ByteFunctional.toByteTraceAlignment
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    (source : ExactTag73GammaRestoredK14ByteFunctional transitionFuel
      configuration projection fixedInstance decoder clean) :
    ExactTag73GammaRestoredK14ByteTraceAlignment transitionFuel configuration
      projection fixedInstance decoder clean where
  words := source.fibreWords
  defaultResponse := source.defaultResponse
  defaultDisclosedFinal := source.defaultDisclosedFinal
  defaultSchedule := source.defaultSchedule
  defaultSelected := source.defaultSelected
  exactAt := by
    intro hidden answers cleanMember input k13 failure
    obtain ⟨decoded, run, bytesExact⟩ :=
      source.decoderAt hidden answers cleanMember input k13 failure
    let coordinates := exactCompilerRestoredGammaCoordinates transitionFuel
      configuration hidden answers
    let actual : GammaRestoredK14ByteFibreWitness transitionFuel configuration
        projection fixedInstance decoder clean hidden coordinates.1 :=
      { answers := answers
        cleanMember := cleanMember
        input := input
        k13 := k13
        failure := failure
        decoded := decoded
        run := run
        residualExact := rfl
        bytesExact := bytesExact }
    have existsWitness : Nonempty (GammaRestoredK14ByteFibreWitness
        transitionFuel configuration projection fixedInstance decoder clean
          hidden coordinates.1) := ⟨actual⟩
    refine ⟨decoded, run, ?_, bytesExact⟩
    change k13.certificate.classified.k12.words =
      source.fibreWords hidden coordinates.1
    rw [ExactTag73GammaRestoredK14ByteFunctional.fibreWords,
      dif_pos existsWitness]
    exact source.sameWords hidden coordinates.1 actual
      (Classical.choice existsWitness)

#print axioms GammaRestoredK14ByteFibreWitness
#print axioms
  gamma_restored_k14_byte_fibre_words_eq_of_exact_k12_source
#print axioms
  gamma_restored_k14_byte_fibre_words_eq_of_typed_k12_source
#print axioms ExactTag73GammaRestoredK14ByteFunctional
#print axioms ExactTag73GammaRestoredK14TypedMerkleFunctional
#print axioms
  ExactTag73GammaRestoredK14TypedMerkleFunctional.toByteFunctional
#print axioms ExactTag73GammaRestoredK14ByteFunctional.fibreWords
#print axioms ExactTag73GammaRestoredK14ByteFunctional.toByteTraceAlignment

end
end AspisK1.V7Tag73GammaRestoredK14ByteFunctional
