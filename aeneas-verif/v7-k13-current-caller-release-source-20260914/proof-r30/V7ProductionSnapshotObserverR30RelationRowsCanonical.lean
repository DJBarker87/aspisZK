import V7CallerCurrentReleaseR30RelationFieldsCanonical
import V7ProductionSnapshotObserverR28AcceptedTail
import V7CallerCurrentReleaseR26AcceptedTerminalEndToEnd

/-!
# Canonical relation rows in an accepted production execution

This module specializes the symbolic relation-field decoder proof to the
current fixed-field reader and transfers the result through the exact row
lookups retained by the accepted production tail.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7ProductionSnapshotObserverR30RelationRowsCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26RelationDecodeSemantics
open V7CallerCurrentReleaseR26AcceptedTailComposition
open V7CallerCurrentReleaseR30FixedFieldCanonical
open V7CallerCurrentReleaseR30RelationFieldsCanonical
open AspisV7ProductionSnapshotObserverR28AcceptedTail

abbrev RawQM31 := field.QM31
abbrev Row := Array RawQM31 6#usize

theorem fixed_reader_relation_fields_canonical
    (reader readerOut : v6_onefold.V6FixedFieldReader)
    (decoded : Array Row 4#usize)
    (run :
      v6_transcript.decode_compact_relation_fields
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
          reader = ok (.Ok decoded, readerOut)) :
    DecodedCanonical decoded := by
  apply successful_relation_field_decode_canonical
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    _ reader readerOut decoded run
  intro current value next success
  exact fixed_reader_next_qm31_canonical current next value success

private theorem decoded_index_canonical
    (decoded : Array Row 4#usize) (row : Row) (ordinal : Std.Usize)
    (ordinalBound : ordinal.val < 4)
    (canonical : DecodedCanonical decoded)
    (read : decoded.index_usize ordinal = ok row) :
    CanonicalRelationRow row := by
  exact row_canonical_is_relation_canonical row
    (decoded_index_row_canonical decoded row ordinal ordinalBound canonical read)

theorem accepted_production_tail_relation_rows_canonical
    {hash : AspisV7ProductionSnapshotObserverR28SourceBridge.HashFn}
    {wire : AspisV7ProductionSnapshotObserverR28SourceBridge.Wire}
    {context : v6_transcript.V6TranscriptContext}
    {hidingContext :
      AspisV7ProductionSnapshotObserverR28SourceBridge.HidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {statement : AspisV7ProductionSnapshotObserverR28SourceBridge.Statement}
    {queryFold :
      AspisV7ProductionSnapshotObserverR28ToR26Prechallenge.QueryFold}
    {transcript : AspisV7ProductionSnapshotObserverR28SourceBridge.Transcript}
    {snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot}
    {inner : V7CallerCurrentReleaseR26AcceptedInnerDispatch.AcceptedInnerDispatch
      AspisV7ProductionSnapshotObserverR28ToR26Prechallenge.terminalInst
      AspisV7ProductionSnapshotObserverR28ToR26Prechallenge.queryFoldInst
      AspisV7ProductionSnapshotObserverR28ToR26Prechallenge.prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement queryFold () true transcript (some snapshot)}
    {chain :
      V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge.AcceptedInnerPrechallengeChain
        inner}
    (acceptedTail : AcceptedProductionTail inner chain) :
    CanonicalRelationRow acceptedTail.source.roundOne.relationRow ∧
    CanonicalRelationRow acceptedTail.source.roundTwo.relationRow ∧
    CanonicalRelationRow acceptedTail.source.roundThree.relationRow := by
  let dispatch := chain.prechallengeDispatch
  have allRows : DecodedCanonical dispatch.relationFields :=
    fixed_reader_relation_fields_canonical
      _ dispatch.fieldsAfterRelation dispatch.relationFields
      dispatch.relationFieldsRun
  exact ⟨
    decoded_index_canonical dispatch.relationFields
      acceptedTail.source.roundOne.relationRow 1#usize (by norm_num)
      allRows acceptedTail.source.roundOne.relationRowSuccess,
    decoded_index_canonical dispatch.relationFields
      acceptedTail.source.roundTwo.relationRow 2#usize (by norm_num)
      allRows acceptedTail.source.roundTwo.relationRowSuccess,
    decoded_index_canonical dispatch.relationFields
      acceptedTail.source.roundThree.relationRow 3#usize (by norm_num)
      allRows acceptedTail.source.roundThree.relationRowSuccess⟩

#print axioms fixed_reader_relation_fields_canonical
#print axioms accepted_production_tail_relation_rows_canonical

end V7ProductionSnapshotObserverR30RelationRowsCanonical
