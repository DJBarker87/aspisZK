import FSV8AlignedAlphaChallengeRun
import FSV8AlignedAlphaInitialPairDisposition

/-!
# Initial-state dispositions for every reached alpha squeeze pair

This leaf recursively consumes the actual `AlignedRejectedPath` and attaches
the source-constructed initial lookup disposition to every rejected pair and
to the accepted final pair.  Each stored pair still carries its exact two
query equations and history append equalities.  No freshness or probability
premise is added.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 1600

namespace AspisV8Completion.FSV8AlignedAlphaPairDispositions

open FSOracleExecution FSBoundedTranscript FSLiveChallengeTrace
open FSV8AlignedAlphaSqueezeStep
open FSV8AlignedAlphaChallengeRun
open FSV8AlignedAlphaInitialPairDisposition
open FSV8CandidateOriginTrace
open FSV8AlphaHistoryPhasePrefix
open FSV8V7OracleMachineBridge
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/-- One exact initial-state disposition for every pair in a rejected path.
The `snoc` constructor retains the actual pair object rather than projecting
it to an answer list. -/
inductive RejectedPathPairDispositions
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript} :
    {blocks : List Block} -> {v7 : OracleState} -> {s : Transcript} ->
      AlignedRejectedPath tape finiteTape limits startV7 start blocks v7 s ->
      Prop where
  | base (aligned : FSV8V7StateAlignment.StateAligned tape finiteTape
      startV7 start.oracle)
      (prefixPath : FSV8AlphaHistoryPhasePrefix.RejectedCandidatePrefix
        startV7.history []) :
      RejectedPathPairDispositions (.base aligned prefixPath)
  | snoc {prior : List Block} {v7 : OracleState} {s : Transcript}
      {path : AlignedRejectedPath tape finiteTape limits startV7 start
        prior v7 s}
      (priorDispositions : RejectedPathPairDispositions path)
      (pair : AlignedSqueezePair tape finiteTape limits v7 s)
      (bounded : prior.length < 4)
      (reject : AspisK1.V7Tag73SamplerDecoder.decodeChallengeParameter
        AspisK1.V7Tag73SecureCircleMap.exactSecureCircleParameterMap
        (.alpha 0) (prior ++ [(outputStep tape s).1]) = none)
      (disposition : InitialPairDisposition tape finiteTape limits v7 s pair) :
      RejectedPathPairDispositions
        (.snoc path pair bounded reject)

theorem AlignedRejectedPath.pairDispositions
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript} :
    {blocks : List Block} -> {v7 : OracleState} -> {s : Transcript} ->
    (path : AlignedRejectedPath tape finiteTape limits startV7 start
      blocks v7 s) -> RejectedPathPairDispositions path := by
  intro blocks v7 s path
  induction path with
  | base aligned prefixPath => exact .base aligned prefixPath
  | snoc path pair bounded reject ih =>
      exact .snoc ih pair bounded reject
        (FSV8AlignedAlphaInitialPairDisposition.AlignedSqueezePair.initialDisposition
          pair)

/-- Every rejected pair is fresh at both of its initial lookups. -/
inductive RejectedPathAllFresh
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript} :
    {blocks : List Block} -> {v7 : OracleState} -> {s : Transcript} ->
      {path : AlignedRejectedPath tape finiteTape limits startV7 start
        blocks v7 s} -> RejectedPathPairDispositions path -> Prop where
  | base (aligned) (prefixPath) :
      RejectedPathAllFresh
        (RejectedPathPairDispositions.base aligned prefixPath)
  | snoc {prior : List Block} {v7 : OracleState} {s : Transcript}
      {path : AlignedRejectedPath tape finiteTape limits startV7 start
        prior v7 s}
      (priorDispositions : RejectedPathPairDispositions path)
      (priorFresh : RejectedPathAllFresh priorDispositions)
      (pair : AlignedSqueezePair tape finiteTape limits v7 s)
      (bounded : prior.length < 4) (reject)
      (outputOrigin outputMissing advanceOrigin advanceMissing) :
      RejectedPathAllFresh
        (RejectedPathPairDispositions.snoc priorDispositions pair bounded reject
          (.bothFresh outputOrigin advanceOrigin outputMissing advanceMissing))

/-- The first non-all-fresh evidence is retained as either a mixed advance or
a cached output.  `earlier` transports an already located conflict through
later reached pairs without discarding their dispositions. -/
inductive RejectedPathConflict
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript} :
    {blocks : List Block} -> {v7 : OracleState} -> {s : Transcript} ->
      {path : AlignedRejectedPath tape finiteTape limits startV7 start
        blocks v7 s} -> RejectedPathPairDispositions path -> Prop where
  | advanceCached {prior : List Block} {v7 : OracleState} {s : Transcript}
      {path : AlignedRejectedPath tape finiteTape limits startV7 start
        prior v7 s}
      (priorDispositions : RejectedPathPairDispositions path)
      (pair : AlignedSqueezePair tape finiteTape limits v7 s)
      (bounded : prior.length < 4)
      (reject : decodeChallengeParameter exactSecureCircleParameterMap
        (.alpha 0) (prior ++ [(outputStep tape s).1]) = none)
      (outputOrigin advanceOrigin outputMissing entry advanceFound) :
      RejectedPathConflict
        (RejectedPathPairDispositions.snoc priorDispositions pair bounded reject
          (.outputFreshAdvanceCached outputOrigin advanceOrigin outputMissing
            entry advanceFound))
  | outputCached {prior : List Block} {v7 : OracleState} {s : Transcript}
      {path : AlignedRejectedPath tape finiteTape limits startV7 start
        prior v7 s}
      (priorDispositions : RejectedPathPairDispositions path)
      (pair : AlignedSqueezePair tape finiteTape limits v7 s)
      (bounded : prior.length < 4)
      (reject : decodeChallengeParameter exactSecureCircleParameterMap
        (.alpha 0) (prior ++ [(outputStep tape s).1]) = none)
      (outputOrigin entry outputFound) :
      RejectedPathConflict
        (RejectedPathPairDispositions.snoc priorDispositions pair bounded reject
          (.outputCached outputOrigin entry outputFound))
  | earlier {prior : List Block} {v7 : OracleState} {s : Transcript}
      {path : AlignedRejectedPath tape finiteTape limits startV7 start
        prior v7 s} {priorDispositions : RejectedPathPairDispositions path}
      (conflict : RejectedPathConflict priorDispositions)
      (pair : AlignedSqueezePair tape finiteTape limits v7 s)
      (bounded : prior.length < 4)
      (reject : decodeChallengeParameter exactSecureCircleParameterMap
        (.alpha 0) (prior ++ [(outputStep tape s).1]) = none)
      (disposition : InitialPairDisposition tape finiteTape limits v7 s pair) :
      RejectedPathConflict
        (RejectedPathPairDispositions.snoc priorDispositions pair bounded reject
          disposition)

theorem rejected_path_all_fresh_or_conflict
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {v7 : OracleState} {s : Transcript}
    {path : AlignedRejectedPath tape finiteTape limits startV7 start
      blocks v7 s} (dispositions : RejectedPathPairDispositions path) :
    RejectedPathAllFresh dispositions ∨ RejectedPathConflict dispositions := by
  induction dispositions with
  | base aligned prefixPath => exact Or.inl (.base aligned prefixPath)
  | snoc priorDispositions pair bounded reject disposition ih =>
      rcases ih with priorFresh | priorConflict
      · cases disposition with
        | bothFresh outputOrigin advanceOrigin outputMissing advanceMissing =>
            exact Or.inl (.snoc priorDispositions priorFresh pair bounded reject outputOrigin
              outputMissing advanceOrigin advanceMissing)
        | outputFreshAdvanceCached outputOrigin advanceOrigin outputMissing
            entry advanceFound =>
            exact Or.inr (.advanceCached priorDispositions pair bounded reject outputOrigin
              advanceOrigin outputMissing entry advanceFound)
        | outputCached outputOrigin entry outputFound =>
            exact Or.inr (.outputCached priorDispositions pair bounded reject outputOrigin entry
              outputFound)
      · exact Or.inr (.earlier priorConflict pair bounded reject disposition)

/-- Exhaustive first-conflict summary for a successful challenge.  A conflict
inside the rejected path is retained recursively; otherwise the final pair is
classified into the same three source cases. -/
inductive SuccessfulPairOriginSummary
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {v7 : OracleState} {s : Transcript}
    {path : AlignedRejectedPath tape finiteTape limits startV7 start
      blocks v7 s} (rejectedDispositions : RejectedPathPairDispositions path)
    {finalPair : AlignedSqueezePair tape finiteTape limits v7 s}
    (finalDisposition : InitialPairDisposition tape finiteTape limits v7 s
      finalPair) : Prop where
  | allFresh
      (priorFresh : RejectedPathAllFresh rejectedDispositions)
      (outputOrigin advanceOrigin outputMissing advanceMissing)
      (finalExact : finalDisposition =
        .bothFresh outputOrigin advanceOrigin outputMissing advanceMissing)
  | rejectedConflict
      (conflict : RejectedPathConflict rejectedDispositions)
  | finalAdvanceCached
      (priorFresh : RejectedPathAllFresh rejectedDispositions)
      (outputOrigin advanceOrigin outputMissing entry advanceFound)
      (finalExact : finalDisposition =
        .outputFreshAdvanceCached outputOrigin advanceOrigin outputMissing
          entry advanceFound)
  | finalOutputCached
      (priorFresh : RejectedPathAllFresh rejectedDispositions)
      (outputOrigin entry outputFound)
      (finalExact : finalDisposition =
        .outputCached outputOrigin entry outputFound)

theorem successful_pair_origin_summary
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {v7 : OracleState} {s : Transcript}
    {path : AlignedRejectedPath tape finiteTape limits startV7 start
      blocks v7 s} (rejectedDispositions : RejectedPathPairDispositions path)
    {finalPair : AlignedSqueezePair tape finiteTape limits v7 s}
    (finalDisposition : InitialPairDisposition tape finiteTape limits v7 s
      finalPair) :
    SuccessfulPairOriginSummary rejectedDispositions finalDisposition := by
  rcases rejected_path_all_fresh_or_conflict rejectedDispositions with
    priorFresh | priorConflict
  · cases finalDisposition with
    | bothFresh outputOrigin advanceOrigin outputMissing advanceMissing =>
        exact .allFresh priorFresh outputOrigin advanceOrigin outputMissing
          advanceMissing rfl
    | outputFreshAdvanceCached outputOrigin advanceOrigin outputMissing entry
        advanceFound =>
        exact .finalAdvanceCached priorFresh outputOrigin advanceOrigin
          outputMissing entry advanceFound rfl
    | outputCached outputOrigin entry outputFound =>
        exact .finalOutputCached priorFresh outputOrigin entry outputFound rfl
  · exact .rejectedConflict priorConflict

/-- The full successful challenge exposes dispositions for all rejected
pairs and the accepted final pair, without changing the existential witnesses
chosen by `SuccessfulAlignedChallenge`. -/
theorem SuccessfulAlignedChallenge.constructs_pair_dispositions
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {final : Transcript}
    {value : Qm31Bytes}
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value) :
    ∃ rejected finalStart beforeFinal,
      ∃ path : AlignedRejectedPath tape finiteTape limits startV7 start
        rejected beforeFinal finalStart,
      ∃ finalPair : AlignedSqueezePair tape finiteTape limits
        beforeFinal finalStart,
        blocks = rejected ++ [(outputStep tape finalStart).1] ∧
        final = (squeeze tape finalStart).2 ∧
        AspisK1.V7Tag73SamplerDecoder.decodeChallengeParameter
          AspisK1.V7Tag73SecureCircleMap.exactSecureCircleParameterMap
          (.alpha 0) (rejected ++ [(outputStep tape finalStart).1]) =
            some value ∧
        relationAlphaHistoryPhase 0
          finalPair.afterAdvance.history = .inactive ∧
        RejectedPathPairDispositions path ∧
        InitialPairDisposition tape finiteTape limits beforeFinal finalStart
          finalPair := by
  rcases success with
    ⟨rejected, finalStart, beforeFinal, path, finalPair, blocksExact,
      finalExact, accepted, finalPhase⟩
  exact ⟨rejected, finalStart, beforeFinal, path, finalPair, blocksExact,
    finalExact, accepted, finalPhase,
    AspisV8Completion.FSV8AlignedAlphaPairDispositions.AlignedRejectedPath.pairDispositions
      path,
    FSV8AlignedAlphaInitialPairDisposition.AlignedSqueezePair.initialDisposition
      finalPair⟩

#print axioms AlignedRejectedPath.pairDispositions
#print axioms rejected_path_all_fresh_or_conflict
#print axioms successful_pair_origin_summary
#print axioms SuccessfulAlignedChallenge.constructs_pair_dispositions

end
end AspisV8Completion.FSV8AlignedAlphaPairDispositions
