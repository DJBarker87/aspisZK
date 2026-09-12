import AspisFormal.K1.V7Tag73K13CleanCausalSourceFromFunctional
import AspisFormal.K1.V7Tag73K13CleanProbabilityClosure
import AspisFormal.K1.V7Tag73K13ViewPrefixFactorization
import AspisFormal.K1.V7Tag73PreQ16OperationalActualLawBounds

/-!
# Candidate-directed operational K1.3 closure

The adversary may expose the post-q16 query-batch coordinate before the
verifier assigns it a logical role.  The exact production router therefore
pre-fixes one of the 512 possible q16 terminal slots and pays the finite
512-way union.  This file installs that honest cost in the complete corrected
pre-q16 K1.3 event ledger.

No work factor is used to normalize an error probability.  The 31- and
34-bit work trials cancel only their corresponding finite trial unions in the
kernel-checked candidate-directed probability theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

namespace AspisK1.V7Tag73K13CandidateDirectedOperationalClosure

open Module
open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CandidateDirectedQueryBatchAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13BoundChallengeClosure
open AspisK1.V7Tag73K13CandidateDirectedSourceBridge
open AspisK1.V7Tag73K13CandidateDirectedViewFunctional
open AspisK1.V7Tag73K13CleanCausalSourceFromFunctional
open AspisK1.V7Tag73K13CleanViewFunctional
open AspisK1.V7Tag73K13CleanProbabilityClosure
open AspisK1.V7Tag73K13ViewPrefixFactorization
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16TargetProbability
open AspisK1.V7Tag73K13RestrictedLaterAlphaActualLawClosure
open AspisK1.V7Tag73PreQ16OperationalActualLawBounds
open AspisK1.V7Tag73PreQ16OperationalMeasuredComposition
open AspisK1.V7Tag73PreQ16OperationalStageAssembly
open AspisK1.V7Tag73PreQ16OperationalStageEvents
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73RelationTailSourceComposition
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Honest corrected K1.3 ledger after paying the complete 512-candidate
query-batch cover.  The chronological Merkle-target term remains separate. -/
def candidateDirectedPreQ16OperationalK13RawError
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  q16SemanticOneForestRawError + exactOneFoldIdealRawError +
    candidateDirectedJointBatchRawError + exactLaterRelationAlphaIdealRawError +
      exactPreQ16LateTargetRawError parameters

/-- The five-event operational K1.3 composition with the honest
candidate-directed joint-batch charge. -/
theorem exact_preQ16_operational_k13_clean_candidate_directed_error_measure_bound
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
        candidateDirectedJointBatchRawError)
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
      candidateDirectedPreQ16OperationalK13RawError parameters := by
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
          candidateDirectedJointBatchRawError) +
          exactLaterRelationAlphaIdealRawError) +
        exactPreQ16LateTargetRawError parameters :=
      add_le_add
        (add_le_add (add_le_add (add_le_add q16Bound oneFoldBound) jointBound)
          laterBound) lateTargetBound
    _ = candidateDirectedPreQ16OperationalK13RawError parameters := by
      unfold candidateDirectedPreQ16OperationalK13RawError
      ac_rfl

/-- Release-facing candidate-directed K1.3 bound.  The only remaining
protocol/source input is the pre-challenge source factorization through the
fixed candidate-directed coordinate key; the exact scheduler coordinate and
probability accounting are internal. -/
theorem exact_tag73_preQ16_operational_k13_candidate_directed_probability_le_of_view_functional
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
    (environment : ExactPreQ16OperationalStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (relationSource : ExactTag73RelationSourceEnvironment transitionFuel
      configuration projection fixedInstance decoder)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34)
    (viewFunctional : ExactCleanCandidateDirectedK13ViewFunctional
      transitionFuel
      configuration projection fixedInstance decoder
        (relationSource.toK13SourceObligations transitionFuel configuration
          projection fixedInstance decoder))
    (laterAlphaSource : ExactTag73RestrictedK13LaterAlphaSource transitionFuel
      configuration projection fixedInstance decoder
      (relationSource.toK13SourceObligations transitionFuel configuration
        projection fixedInstance decoder)
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          k13CircleListDecodeErrorEvent
            (exactTag73PreQ16OperationalStages transitionFuel configuration
              projection fixedInstance decoder decoderBinding basis rc poseidon
              transitionRoom (by omega) initialEncoderExact environment)) ≤
      candidateDirectedPreQ16OperationalK13RawError parameters := by
  let clean := exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
    projection fixedInstance
  let source := relationSource.toK13SourceObligations transitionFuel
    configuration projection fixedInstance decoder
  have q16Bound :=
    exact_clean_preQ16_trial_union_probability_le_one_forest_of_bindings
      (decoder := decoder) hiddenLaw environment.toDecodedParsedSourceProvider
      transitionRoom (by omega)
      (fun sample input schedule ↦
        (environment.k13Source sample input).frontierExact schedule)
      reference traceExists foldExposureCap finalExposureCap
  have oneFoldBound :=
    exact_clean_bidirectional_preQ16_onefold_probability_le hiddenLaw
      transitionRoom (by omega) initialEncoderExact finalEncoderExact
      environment.toDecodedParsedSourceProvider foldExposureCap
  have jointBound :=
    exact_clean_candidate_directed_joint_batch_collision_probability_le
      hiddenLaw source
      (AspisK1.V7Tag73K13CleanCausalSourceFromFunctional.ExactCleanCandidateDirectedK13ViewFunctional.toCausalSource
        viewFunctional transitionRoom programmedCover)
      (by simpa [exact_compiler_exposure_trial_card] using foldExposureCap)
      (by simpa [exact_compiler_exposure_trial_card] using finalExposureCap)
  have laterBound := exact_tag73_restricted_k13_later_alpha_probability_le
    hiddenLaw source clean laterAlphaSource
  have lateBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ exactK13PreQ16MerkleTargetHitEvent configuration
            transitionFuel) ≤ exactPreQ16LateTargetRawError parameters :=
    ((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
      Set.inter_subset_right).trans
        (exact_k13_preQ16_merkle_target_hit_probability_le hiddenLaw
          configuration transitionFuel)
  exact
    exact_preQ16_operational_k13_clean_candidate_directed_error_measure_bound
      hiddenLaw transitionFuel configuration projection fixedInstance decoder
      decoderBinding basis rc poseidon transitionRoom (by omega)
      initialEncoderExact environment source q16Bound oneFoldBound jointBound
      laterBound lateBound

/-- Release-facing K1.3 closure from the literal production-prefix
factorization.  This removes the abstract functional-view premise from the
operational theorem: the scheduler proves common prefixes, while the source
bridge need only prove that the maintained algebraic view is decoded from that
prefix. -/
theorem exact_tag73_preQ16_operational_k13_candidate_directed_probability_le_of_prefix_factorization
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
    (environment : ExactPreQ16OperationalStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (relationSource : ExactTag73RelationSourceEnvironment transitionFuel
      configuration projection fixedInstance decoder)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34)
    (factorization : ExactCandidateDirectedK13ViewPrefixFactorization
      transitionFuel configuration projection fixedInstance decoder
        (relationSource.toK13SourceObligations transitionFuel configuration
          projection fixedInstance decoder))
    (laterAlphaSource : ExactTag73RestrictedK13LaterAlphaSource transitionFuel
      configuration projection fixedInstance decoder
      (relationSource.toK13SourceObligations transitionFuel configuration
        projection fixedInstance decoder)
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          k13CircleListDecodeErrorEvent
            (exactTag73PreQ16OperationalStages transitionFuel configuration
              projection fixedInstance decoder decoderBinding basis rc poseidon
              transitionRoom (by omega) initialEncoderExact environment)) ≤
      candidateDirectedPreQ16OperationalK13RawError parameters := by
  exact
    exact_tag73_preQ16_operational_k13_candidate_directed_probability_le_of_view_functional
      hiddenLaw transitionFuel configuration projection fixedInstance decoder
      decoderBinding basis rc poseidon environment relationSource transitionRoom
      programmedCover initialEncoderExact finalEncoderExact reference traceExists
      foldExposureCap finalExposureCap
      (factorization.toCleanViewFunctional transitionRoom programmedCover)
      laterAlphaSource

#print axioms candidateDirectedPreQ16OperationalK13RawError
#print axioms
  exact_preQ16_operational_k13_clean_candidate_directed_error_measure_bound
#print axioms
  exact_tag73_preQ16_operational_k13_candidate_directed_probability_le_of_view_functional
#print axioms
  exact_tag73_preQ16_operational_k13_candidate_directed_probability_le_of_prefix_factorization

end
end AspisK1.V7Tag73K13CandidateDirectedOperationalClosure
