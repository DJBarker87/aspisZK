import FSV8AlignedAlphaNamedSlotsNodup

/-!
# Exact local-history slot bridge for one accepted alpha chronology

This leaf identifies the path-indexed fresh-slot list with a direct replay of
the actual V7 query-record suffix.  The replay computes each relation-alpha
label from the history available immediately before that record and retains a
label only when that literal record is fresh.

This closes the local-history half of the exact-root label bridge.  Connecting
this replay to `alpha0RootLabeledRecords` still requires the scheduler replay
theorem saying that each projected machine-fresh root record exposes the same
V7 state/input at that chronological cut.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8AlignedAlphaHistorySlotBridge

open FSBoundedTranscript
open FSV8AlignedAlphaSqueezeStep FSV8AlignedAlphaChallengeRun
open FSV8AlignedAlphaNamedSlotsNodup FSV8CandidateOriginTrace
open FSV8AlphaHistoryPhasePrefix
open FSV8V7OracleMachineBridge
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/-- Keep a pre-answer label exactly when the source record is a fresh oracle
exposure. -/
def retainFreshLabel (origin : AnswerOrigin)
    (label : Option RelationAlphaDuplexSlot) :
    List RelationAlphaDuplexSlot :=
  match origin, label with
  | .fresh, some slot => [slot]
  | _, _ => []

/-- Replay relation-alpha labels over an actual chronological record suffix.
The accumulated history is extended after every record, including cached
records, while only fresh records expose a root-tape coordinate. -/
def freshRelationSlotsFrom :
    List QueryRecord → List QueryRecord → List RelationAlphaDuplexSlot
  | _history, [] => []
  | history, record :: rest =>
      retainFreshLabel record.origin
          (relationAlphaPreferredSlotFromHistory 0 history record.input) ++
        freshRelationSlotsFrom (history ++ [record]) rest

theorem fresh_relation_slots_from_append
    (history first second : List QueryRecord) :
    freshRelationSlotsFrom history (first ++ second) =
      freshRelationSlotsFrom history first ++
        freshRelationSlotsFrom (history ++ first) second := by
  induction first generalizing history with
  | nil => simp [freshRelationSlotsFrom]
  | cons record rest ih =>
      simp only [List.cons_append, freshRelationSlotsFrom]
      rw [ih]
      simp [List.append_assoc]

theorem retain_fresh_label_some (origin : AnswerOrigin)
    (slot : RelationAlphaDuplexSlot) :
    retainFreshLabel origin (some slot) = freshSlot origin slot := by
  cases origin <;> rfl

/-- The actual output/advance records of the next source pair replay to the
two path-indexed slots, with cached halves omitted. -/
theorem rejected_prefix_pair_slots
    {history : List QueryRecord} {prior : List Block}
    (pathPrefix : RejectedCandidatePrefix history prior)
    (bounded : prior.length < 4) (digest output advanced : Block)
    (outputOrigin advanceOrigin : AnswerOrigin) :
    freshRelationSlotsFrom history
        [outputRecord digest output outputOrigin,
          advanceRecord digest advanced advanceOrigin] =
      freshSlot outputOrigin (⟨prior.length, bounded⟩, 0) ++
        freshSlot advanceOrigin (⟨prior.length, bounded⟩, 1) := by
  obtain ⟨outputSlot, advanceSlot⟩ :=
    rejectedCandidatePrefix_next_slots pathPrefix bounded digest output outputOrigin
  simp only [freshRelationSlotsFrom, List.append_assoc,
    List.append_nil]
  rw [show
      relationAlphaPreferredSlotFromHistory 0 history
          (outputRecord digest output outputOrigin).input =
        some (⟨prior.length, bounded⟩, 0) by
      simpa [outputRecord, AspisK1.V7Tag73TranscriptSchedule.bytes,
        AspisK1.V7Tag73TranscriptSchedule.domSqueeze] using outputSlot]
  rw [show
      relationAlphaPreferredSlotFromHistory 0
          (history ++ [outputRecord digest output outputOrigin])
          (advanceRecord digest advanced advanceOrigin).input =
        some (⟨prior.length, bounded⟩, 1) by
      simpa [advanceRecord, AspisK1.V7Tag73TranscriptSchedule.bytes,
        AspisK1.V7Tag73TranscriptSchedule.domAdvance] using advanceSlot]
  rw [retain_fresh_label_some, retain_fresh_label_some]
  simp [outputRecord, advanceRecord]

/-- A path-indexed slot proof is exactly the direct chronological replay of
one concrete suffix of the path's actual V7 history.  The suffix and equality
are constructed by induction from the source path; neither is assumed. -/
theorem AlignedPathFreshSlots.exact_history_replay
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {v7 : OracleState} {s : Transcript}
    {path : AlignedRejectedPath tape finiteTape limits startV7 start
      blocks v7 s}
    {slots : List RelationAlphaDuplexSlot}
    (source : AlignedPathFreshSlots path slots) :
    ∃ suffix,
      v7.history = startV7.history ++ suffix ∧
      freshRelationSlotsFrom startV7.history suffix = slots := by
  induction source with
  | base aligned prefixPath =>
      exact ⟨[], by simp, rfl⟩
  | @snoc prior v7 s path pair bounded reject slots source ih =>
      rcases ih with ⟨suffix, historyExact, slotsExact⟩
      let outputRecord' := outputRecord s.digest (outputStep tape s).1
        pair.outputOrigin
      let advanceRecord' := advanceRecord s.digest (advanceStep tape s).1
        pair.advanceOrigin
      refine ⟨suffix ++ [outputRecord', advanceRecord'], ?_, ?_⟩
      · rw [pair.advanceHistory, pair.outputHistory, historyExact]
        simp [outputRecord', advanceRecord', List.append_assoc]
      · rw [fresh_relation_slots_from_append, slotsExact]
        have currentPrefix := path.prefixPath
        have pairSlots := rejected_prefix_pair_slots currentPrefix bounded s.digest
          (outputStep tape s).1 (advanceStep tape s).1 pair.outputOrigin
          pair.advanceOrigin
        rw [historyExact] at pairSlots
        simpa [outputRecord', advanceRecord', List.append_assoc] using pairSlots

/-- The successful one-marker chronology constructs the exact fresh-slot
replay through all rejected pairs and the accepted pair, and that replay is
duplicate-free. -/
theorem successful_aligned_candidate_exact_nodup_history_replay
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {final : Transcript} {value : Qm31Bytes}
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value)
    (blocksCap : blocks.length ≤ 4) :
    ∃ suffix,
      final.oracle.log = (startV7.history ++ suffix).map projectRecord ∧
      (freshRelationSlotsFrom startV7.history suffix).Nodup := by
  rcases success with
    ⟨rejected, finalStart, beforeFinal, path, finalPair, blocksExact,
      finalExact, accepted, finalPhase⟩
  obtain ⟨slots, pathSlots⟩ :=
    AlignedRejectedPath.constructs_candidate_fresh_slots path
  obtain ⟨priorSuffix, beforeHistory, priorSlotsExact⟩ :=
    AlignedPathFreshSlots.exact_history_replay pathSlots
  have bounded : rejected.length < 4 := by
    rw [blocksExact] at blocksCap
    simp only [List.length_append, List.length_singleton] at blocksCap
    omega
  let outputRecord' := outputRecord finalStart.digest
    (outputStep tape finalStart).1 finalPair.outputOrigin
  let advanceRecord' := advanceRecord finalStart.digest
    (advanceStep tape finalStart).1 finalPair.advanceOrigin
  let suffix := priorSuffix ++ [outputRecord', advanceRecord']
  refine ⟨suffix, ?_, ?_⟩
  · rw [finalExact]
    calc
      (squeeze tape finalStart).2.oracle.log =
          finalPair.afterAdvance.history.map projectRecord :=
        finalPair.aligned.history
      _ = (startV7.history ++ suffix).map projectRecord := by
        rw [finalPair.advanceHistory, finalPair.outputHistory, beforeHistory]
        simp [suffix, outputRecord', advanceRecord', List.append_assoc]
  · rw [fresh_relation_slots_from_append, priorSlotsExact]
    have finalSlots := rejected_prefix_pair_slots path.prefixPath bounded
      finalStart.digest (outputStep tape finalStart).1
      (advanceStep tape finalStart).1 finalPair.outputOrigin
      finalPair.advanceOrigin
    rw [beforeHistory] at finalSlots
    rw [show freshRelationSlotsFrom (startV7.history ++ priorSuffix)
        [outputRecord', advanceRecord'] =
          freshSlot finalPair.outputOrigin (⟨rejected.length, bounded⟩, 0) ++
            freshSlot finalPair.advanceOrigin
              (⟨rejected.length, bounded⟩, 1) by
      simpa [outputRecord', advanceRecord'] using finalSlots]
    simpa [List.append_assoc] using
      (candidate_fresh_slots_append_final_nodup
        pathSlots.candidate_source bounded finalPair.outputOrigin
          finalPair.advanceOrigin)

#print axioms fresh_relation_slots_from_append
#print axioms rejected_prefix_pair_slots
#print axioms AlignedPathFreshSlots.exact_history_replay
#print axioms successful_aligned_candidate_exact_nodup_history_replay

end
end AspisV8Completion.FSV8AlignedAlphaHistorySlotBridge
