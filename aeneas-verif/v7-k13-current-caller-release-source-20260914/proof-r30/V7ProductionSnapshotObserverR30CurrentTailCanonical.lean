import V7ProductionSnapshotObserverR30InitialFoldTail
import V7CallerCurrentReleaseR30Final256Canonical
import V7ProductionSnapshotObserverR30RelationRowsCanonical
import V7ProductionSnapshotObserverR30ChallengesCanonical
import V7CallerCurrentReleaseR30ChallengeNonzeroCanonical

/-!
# Canonical data retained by the current production initial-fold tail

The accepted tail below is bound to the exact current initial-fold dispatch.
These lemmas reuse the symbolic decoder and sampler proofs over that dispatch,
without selecting a separate historical tail witness.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace AspisV7ProductionSnapshotObserverR30CurrentTailCanonical

open AspisV7ProductionSnapshotObserverR28SourceBridge
open AspisV7ProductionSnapshotObserverR28ToR26Prechallenge
open AspisV7ProductionSnapshotObserverR30InitialFoldTail
open V7CallerCurrentReleaseR26AcceptedInnerDispatch
open V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge
open V7CallerCurrentReleaseR30FixedFieldCanonical
open V7CallerCurrentReleaseR30Final256Canonical
open V7CallerCurrentReleaseR26FoldValuesPrefixSemantics
open V7CallerCurrentReleaseR26RelationDecodeSemantics
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR30ChallengeCanonical
open V7CallerCurrentReleaseR30ChallengeNonzeroCanonical
open V7CallerCurrentReleaseR30RelationFieldsCanonical
open V7ProductionSnapshotObserverR30RelationRowsCanonical
open V7ProductionSnapshotObserverR30ChallengesCanonical

abbrev RawQM31 := field.QM31
abbrev Row := Array RawQM31 6#usize

private theorem decoded_index_canonical
    (decoded : Array Row 4#usize) (row : Row) (ordinal : Std.Usize)
    (ordinalBound : ordinal.val < 4)
    (canonical : DecodedCanonical decoded)
    (read : decoded.index_usize ordinal = ok row) :
    CanonicalRelationRow row := by
  exact row_canonical_is_relation_canonical row
    (decoded_index_row_canonical decoded row ordinal ordinalBound canonical read)

/-- The current dispatch's final 256 values come directly from fixed-field
reading and therefore satisfy the representation invariant required by the
terminal relation theorem. -/
theorem accepted_current_fold_tail_final256_canonical
    {hash : HashFn} {wire : Wire}
    {context : v6_transcript.V6TranscriptContext}
    {hidingContext : HidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {statement : Statement} {queryFold : QueryFold}
    {transcript : AspisV7ProductionSnapshotObserverR28SourceBridge.Transcript}
    {snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot}
    {inner : AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement queryFold () true transcript (some snapshot)}
    {chain : AcceptedInnerPrechallengeChain inner}
    {prepared : V7CallerCurrentReleaseR30OuterAccumulator.AcceptedPreparedAccumulator
      chain.outer}
    {accumulator : V7CallerCurrentReleaseR30CircleAccumulator.AcceptedCircleAccumulator
      prepared}
    {dispatch : V7CallerCurrentReleaseR30InitialPrechallengeDispatch.AcceptedInitialPrechallengeDispatch
      accumulator.origin}
    (_current : AcceptedCurrentFoldTail dispatch) :
    CanonicalValues dispatch.foldedValues := by
  have canonical : CanonicalFinal256 dispatch.foldedValues :=
    successful_decode_and_absorb_final256_canonical
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
      (fun current value next success =>
        fixed_reader_next_qm31_canonical current next value success)
      dispatch.transcriptBeforeFinal dispatch.transcriptAfterFinalValues
      dispatch.fieldsAfterRelation dispatch.fieldsAfterFinal
      dispatch.foldedValues dispatch.foldedValuesRun
  intro index indexBound
  exact canonical index (by simpa [Array.length_eq] using indexBound)

/-- The relation rows selected by the exact current dispatch are canonical. -/
theorem accepted_current_fold_tail_relation_rows_canonical
    {hash : HashFn} {wire : Wire}
    {context : v6_transcript.V6TranscriptContext}
    {hidingContext : HidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {statement : Statement} {queryFold : QueryFold}
    {transcript : AspisV7ProductionSnapshotObserverR28SourceBridge.Transcript}
    {snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot}
    {inner : AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement queryFold () true transcript (some snapshot)}
    {chain : AcceptedInnerPrechallengeChain inner}
    {prepared : V7CallerCurrentReleaseR30OuterAccumulator.AcceptedPreparedAccumulator
      chain.outer}
    {accumulator : V7CallerCurrentReleaseR30CircleAccumulator.AcceptedCircleAccumulator
      prepared}
    {dispatch : V7CallerCurrentReleaseR30InitialPrechallengeDispatch.AcceptedInitialPrechallengeDispatch
      accumulator.origin}
    (current : AcceptedCurrentFoldTail dispatch) :
    CanonicalRelationRow current.source.roundOne.relationRow ∧
    CanonicalRelationRow current.source.roundTwo.relationRow ∧
    CanonicalRelationRow current.source.roundThree.relationRow := by
  have allRows : DecodedCanonical dispatch.relationFields :=
    fixed_reader_relation_fields_canonical
      _ dispatch.fieldsAfterRelation dispatch.relationFields
      dispatch.relationFieldsRun
  exact ⟨
    decoded_index_canonical dispatch.relationFields
      current.source.roundOne.relationRow 1#usize (by norm_num)
      allRows current.source.roundOne.relationRowSuccess,
    decoded_index_canonical dispatch.relationFields
      current.source.roundTwo.relationRow 2#usize (by norm_num)
      allRows current.source.roundTwo.relationRowSuccess,
    decoded_index_canonical dispatch.relationFields
      current.source.roundThree.relationRow 3#usize (by norm_num)
      allRows current.source.roundThree.relationRowSuccess⟩

/-- The three relation-round challenge samples retained in the current tail
are canonical field values. -/
theorem accepted_current_fold_tail_challenges_canonical
    {hash : HashFn} {wire : Wire}
    {context : v6_transcript.V6TranscriptContext}
    {hidingContext : HidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {statement : Statement} {queryFold : QueryFold}
    {transcript : AspisV7ProductionSnapshotObserverR28SourceBridge.Transcript}
    {snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot}
    {inner : AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement queryFold () true transcript (some snapshot)}
    {chain : AcceptedInnerPrechallengeChain inner}
    {prepared : V7CallerCurrentReleaseR30OuterAccumulator.AcceptedPreparedAccumulator
      chain.outer}
    {accumulator : V7CallerCurrentReleaseR30CircleAccumulator.AcceptedCircleAccumulator
      prepared}
    {dispatch : V7CallerCurrentReleaseR30InitialPrechallengeDispatch.AcceptedInitialPrechallengeDispatch
      accumulator.origin}
    (current : AcceptedCurrentFoldTail dispatch) :
    GeneratedCanonicalQM31 current.source.roundOne.alphaOne ∧
    GeneratedCanonicalQM31 current.source.roundTwo.alphaTwo ∧
    GeneratedCanonicalQM31 current.source.roundThree.alphaThree := by
  exact ⟨
    successful_challenge_qm31_canonical
      current.source.roundOne.transcriptAbsorb
      current.source.roundOne.transcriptChallenge
      current.source.roundOne.alphaOne
      current.source.roundOne.challengeSuccess,
    successful_challenge_qm31_canonical
      current.source.roundTwo.transcriptAbsorb
      current.source.roundTwo.transcriptChallenge
      current.source.roundTwo.alphaTwo
      current.source.roundTwo.challengeSuccess,
    successful_challenge_qm31_canonical
      current.source.roundThree.transcriptAbsorb
      current.source.roundThree.transcriptChallenge
      current.source.roundThree.alphaThree
      current.source.roundThree.challengeSuccess⟩

/-- The scale passed into the literal query-batch insertion comes from the
successful nonzero transcript sample retained with this exact production tail. -/
theorem accepted_current_fold_tail_query_batch_challenge_canonical
    {hash : HashFn} {wire : Wire}
    {context : v6_transcript.V6TranscriptContext}
    {hidingContext : HidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {statement : Statement} {queryFold : QueryFold}
    {transcript : AspisV7ProductionSnapshotObserverR28SourceBridge.Transcript}
    {snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot}
    {inner : AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement queryFold () true transcript (some snapshot)}
    {chain : AcceptedInnerPrechallengeChain inner}
    {prepared : V7CallerCurrentReleaseR30OuterAccumulator.AcceptedPreparedAccumulator
      chain.outer}
    {accumulator : V7CallerCurrentReleaseR30CircleAccumulator.AcceptedCircleAccumulator
      prepared}
    {dispatch : V7CallerCurrentReleaseR30InitialPrechallengeDispatch.AcceptedInitialPrechallengeDispatch
      accumulator.origin}
    (current : AcceptedCurrentFoldTail dispatch) :
    GeneratedCanonicalQM31 current.tail.queryBatchChallenge := by
  rcases current.tail.queryBatchChallengeRun with
    ⟨transcriptAbsorbed, transcriptAfterChallenge, challengeRun⟩
  exact successful_challenge_nonzero_qm31_canonical transcriptAbsorbed
    transcriptAfterChallenge current.tail.queryBatchChallenge challengeRun

#print axioms accepted_current_fold_tail_final256_canonical
#print axioms accepted_current_fold_tail_relation_rows_canonical
#print axioms accepted_current_fold_tail_challenges_canonical
#print axioms accepted_current_fold_tail_query_batch_challenge_canonical

end AspisV7ProductionSnapshotObserverR30CurrentTailCanonical
