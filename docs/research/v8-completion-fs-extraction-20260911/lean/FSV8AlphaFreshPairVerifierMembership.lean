import FSV8AlignedAlphaSqueezeStep
import FSV8ExactRootFunctionalRun
import FSV8ReturnedBindKnownPrefix
import FSV8MarkerFreshVerifierQueryBridge
import AspisFormal.K1.V7Tag73ExactCompilerGammaTraceOccurrence

/-!
# Fresh alpha-pair records in the returned verifier enumeration

This leaf closes the local record-enumeration part of the alpha router source
bridge.  A fresh output or advance half of an actual `AlignedSqueezePair` is
shown to occur in the exact fresh-query enumeration of any enclosing returned
verifier history.

The sole remaining source fact for each application is the chronological
interval: the pair's entry history must follow the returned verifier entry,
and its `afterAdvance` history must precede the returned verifier final state.
For the selected whole verifier the first inclusion follows from the existing
prefix factorization.  The second is the still-missing post-marker live-alpha
factorization; it may not be inferred merely from a locally fresh origin.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 1600

namespace AspisV8Completion.FSV8AlphaFreshPairVerifierMembership

open FSOracleExecution FSBoundedTranscript
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73VerifierOracleStability
open FSV8AlignedAlphaSqueezeStep
open FSV8AlphaHistoryPhasePrefix
open FSV8CandidateOriginTrace
open FSV8MarkerFreshVerifierQueryBridge

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/-- One chronological interval premise, deliberately kept as a source
ordering fact rather than an acceptance, probability, or target assumption. -/
structure PairInsideVerifierHistory
    (entry pairStart pairEnd finalState : OracleState) : Prop where
  entryToPair : entry.history <+: pairStart.history
  pairToFinal : pairEnd.history <+: finalState.history

/-- A fresh output half of the actual pair occurs in the enclosing verifier's
literal fresh-query enumeration. -/
theorem fresh_output_mem_enclosing_fresh_enumeration
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {s : Transcript}
    (pair : AlignedSqueezePair tape finiteTape limits v7 s)
    (fresh : pair.outputOrigin = .fresh)
    (entry finalState : OracleState)
    (inside : PairInsideVerifierHistory entry v7 pair.afterAdvance finalState) :
    (outputInput s, (outputStep tape s).1) ∈
      freshQueryEnumeration (historySince entry finalState) := by
  have outputExact : pair.afterOutput.history = v7.history ++
      [markerFreshRecord .verifier (outputInput s) (outputStep tape s).1] := by
    simpa [markerFreshRecord, outputRecord, outputInput, fresh,
      AspisK1.V7Tag73TranscriptSchedule.bytes,
      AspisK1.V7Tag73TranscriptSchedule.domSqueeze] using pair.outputHistory
  have outputToEnd : pair.afterOutput.history <+:
      pair.afterAdvance.history := by
    rw [pair.advanceHistory]
    exact List.prefix_append _ _
  exact markerFresh_mem_fresh_enumeration_of_history_prefixes
    entry v7 pair.afterOutput finalState .verifier (outputInput s)
      (outputStep tape s).1 inside.entryToPair outputExact
      (outputToEnd.trans inside.pairToFinal)

/-- A fresh advance half of the same pair occurs in the same enclosing
verifier enumeration. -/
theorem fresh_advance_mem_enclosing_fresh_enumeration
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {s : Transcript}
    (pair : AlignedSqueezePair tape finiteTape limits v7 s)
    (fresh : pair.advanceOrigin = .fresh)
    (entry finalState : OracleState)
    (inside : PairInsideVerifierHistory entry v7 pair.afterAdvance finalState) :
    (advanceInput s, (advanceStep tape s).1) ∈
      freshQueryEnumeration (historySince entry finalState) := by
  have advanceExact : pair.afterAdvance.history = pair.afterOutput.history ++
      [markerFreshRecord .verifier (advanceInput s) (advanceStep tape s).1] := by
    simpa [markerFreshRecord, advanceRecord, advanceInput, fresh,
      AspisK1.V7Tag73TranscriptSchedule.bytes,
      AspisK1.V7Tag73TranscriptSchedule.domAdvance] using pair.advanceHistory
  have entryToOutput : entry.history <+: pair.afterOutput.history := by
    have pairToOutput : v7.history <+: pair.afterOutput.history := by
      rw [pair.outputHistory]
      exact List.prefix_append _ _
    exact inside.entryToPair.trans pairToOutput
  exact markerFresh_mem_fresh_enumeration_of_history_prefixes
    entry pair.afterOutput pair.afterAdvance finalState .verifier
      (advanceInput s) (advanceStep tape s).1 entryToOutput advanceExact
      inside.pairToFinal

#print axioms PairInsideVerifierHistory
#print axioms fresh_output_mem_enclosing_fresh_enumeration
#print axioms fresh_advance_mem_enclosing_fresh_enumeration

end
end AspisV8Completion.FSV8AlphaFreshPairVerifierMembership
