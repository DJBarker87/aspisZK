import AspisFormal.K1.V7Tag73ExactFoldArmedQueryBatchProbabilityReady

/-!
# Candidate-directed K1.3 production coordinate

This small module isolates the exact accepted fold-work, final-work, and
query-batch coordinate selected by the production Tag-73 scheduler.  Keeping
the predicate separate prevents downstream actual-law declarations from
re-elaborating the complete scheduler theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73K13CandidateDirectedCoordinateSelected

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactFoldArmedQueryBatchProbabilityReady
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler

/-- The literal production coordinate selected by one candidate and the two
accepted work trials.  The two trial equalities retain the source provenance
that the routing theorem used to choose those indices; without them the bare
work predicates would also admit unrelated lucky coordinates.  The final
conjunct binds the operational query-batch challenge to the nonzero value
decoded from that exact coordinate. -/
def ExactTag73CandidateDirectedCoordinateSelected
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (candidate : Q16DigestSlot)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters) : Prop :=
  let router := exactCompilerFoldArmedCandidateQueryBatchRouter parameters
    transitionFuel foldTrial.val finalTrial.val candidate
    (exactPlainRomCursor configuration sample.1).erase
  let coordinates :=
    exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
      router sample.2
  foldTrial = (exactAcceptedFoldTrial input).trial ∧
    (∃ transitionRoom : 2 ≤ transitionFuel,
      finalTrial =
        (exactAcceptedDagInstallation transitionRoom input).finalTrial) ∧
    FoldWork31Accepted coordinates.1.2.1 ∧
    FinalWork34Accepted coordinates.1.2.2.2.1 ∧
    ∃ success : GammaPrefixSucceeds coordinates.2,
      exactOperationalChallenge input .queryBatch =
        (routedSuccessfulGammaValue
          (successfulGammaPrefixFlatRoutingEquiv
            ⟨coordinates.2, success⟩)).1

/-- The production routing theorem expressed directly in the factored
coordinate predicate used by the actual-law event partition. -/
theorem exact_operational_input_has_candidate_directed_coordinate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
        (candidate : Q16DigestSlot),
      ExactTag73CandidateDirectedCoordinateSelected input candidate foldTrial
        finalTrial := by
  obtain ⟨foldTrial, finalTrial, candidate, foldTrialExact, finalTrialExact,
      foldAccepted, finalAccepted, success, challengeExact⟩ :=
    exact_selected_fold_armed_query_batch_coordinate_is_successful
      transitionRoom programmedCover input
  refine ⟨foldTrial, finalTrial, candidate, ?_, ⟨transitionRoom, ?_⟩,
    foldAccepted, finalAccepted, success, challengeExact⟩
  · exact foldTrialExact
  · exact finalTrialExact

#print axioms ExactTag73CandidateDirectedCoordinateSelected
#print axioms exact_operational_input_has_candidate_directed_coordinate

end AspisK1.V7Tag73K13CandidateDirectedCoordinateSelected
