import V7CallerCurrentReleaseR26AcceptedPrechallengeDispatch

/-!
# Accepted shared V7 verifier reaches the proved post-prechallenge tail

This module composes the generated control-flow inversions.  Starting from a
successful shared V7 verifier body, it retains the exact prefix, outer loop,
circle loop, terminal body, and post-prechallenge call from one execution.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge

open V7CallerCurrentReleaseR26AcceptedInnerDispatch
open V7CallerCurrentReleaseR26AcceptedOnefoldPrefix
open V7CallerCurrentReleaseR26AcceptedOuterLoop
open V7CallerCurrentReleaseR26AcceptedCircleOrigin
open V7CallerCurrentReleaseR26AcceptedPrechallengeDispatch

abbrev Snapshot := v6_transcript.V6QueryBatchPrechallengeSnapshot

/-- The complete generated dispatch chain from an accepted shared verifier
body to its exact successful post-prechallenge helper call. -/
structure AcceptedInnerPrechallengeChain
    {TerminalCheck QueryFold Prechallenge : Type}
    {terminalInst : core.ops.function.FnOnce TerminalCheck
      v6_transcript.V6SemanticView Bool}
    {queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError)}
    {prechallengeInst : core.ops.function.FnMut Prechallenge
      v6_transcript.V6QueryBatchPrechallengeView Unit}
    {hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)}
    {wire : v7_onefold.V7CompactOneFoldWire}
    {context : v6_transcript.V6TranscriptContext}
    {hidingContext : state_only_hiding.StateOnlyHidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16}
    {checkPow : Bool} {terminalCheck : TerminalCheck}
    {queryFold : QueryFold} {prechallenge : Prechallenge}
    {captureSnapshot : Bool}
    {verified : v6_transcript.V6VerifiedTranscript}
    {returnedSnapshot : Option Snapshot}
    (inner : AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow terminalCheck queryFold prechallenge captureSnapshot verified
      returnedSnapshot) : Type where
  outer : AcceptedOnefoldLoopDispatch queryFoldInst
    (v6_transcript.finish_v7_compact_relation.closure.Insts.CoreOpsFunctionFnOnceTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptError
      queryFoldInst
      (v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple
        terminalInst queryFoldInst prechallengeInst)
      prechallengeInst)
    (v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple
      terminalInst queryFoldInst prechallengeInst)
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    prechallengeInst inner.transcript2 wire.work_nonces wire.c1_frontier
    wire.c2_frontier
    (Array.make 3#usize [v7_onefold.V7_COMPACT_BATCH_WORK_BITS,
      v7_onefold.V7_COMPACT_FOLD_WORK_BITS,
      v7_onefold.V7_COMPACT_FINAL_WORK_BITS])
    0#u8 v7_merkle208.V7_MERKLE_DIGEST_BYTES
    (transcript.label.V7_QUERY_BATCH_CHALLENGE,
      transcript.label.V7_QUERY_BATCH_CLAIM)
    false () inner.fields2 inactiveRowGroups inactiveGroupMasks checkPow
    inner.semanticPoint inner.pointClaims queryFold prechallenge captureSnapshot
    () verified returnedSnapshot
  circle : AcceptedCircleLoopDispatch outer
  origin : AcceptedCircleBodyOrigin circle
  prechallengeDispatch : AcceptedPrechallengeDispatch origin

/-- One successful generated shared-verifier execution supplies the complete
literal dispatch chain to the post-prechallenge helper. -/
theorem AcceptedInnerDispatch.exposesPrechallengeChain
    {TerminalCheck QueryFold Prechallenge : Type}
    {terminalInst : core.ops.function.FnOnce TerminalCheck
      v6_transcript.V6SemanticView Bool}
    {queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError)}
    {prechallengeInst : core.ops.function.FnMut Prechallenge
      v6_transcript.V6QueryBatchPrechallengeView Unit}
    {hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)}
    {wire : v7_onefold.V7CompactOneFoldWire}
    {context : v6_transcript.V6TranscriptContext}
    {hidingContext : state_only_hiding.StateOnlyHidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16}
    {checkPow : Bool} {terminalCheck : TerminalCheck}
    {queryFold : QueryFold} {prechallenge : Prechallenge}
    {captureSnapshot : Bool}
    {verified : v6_transcript.V6VerifiedTranscript}
    {returnedSnapshot : Option Snapshot}
    (inner : AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow terminalCheck queryFold prechallenge captureSnapshot verified
      returnedSnapshot) :
    Nonempty (AcceptedInnerPrechallengeChain inner) := by
  have onefoldSuccess :=
    V7CallerCurrentReleaseR26AcceptedInnerDispatch.AcceptedInnerDispatch.finishOnefoldSuccess
      inner
  obtain ⟨outer⟩ := accepted_onefold_exposes_outer_loop queryFoldInst
    (v6_transcript.finish_v7_compact_relation.closure.Insts.CoreOpsFunctionFnOnceTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptError
      queryFoldInst
      (v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple
        terminalInst queryFoldInst prechallengeInst)
      prechallengeInst)
    (v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple
      terminalInst queryFoldInst prechallengeInst)
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    prechallengeInst inner.transcript2 wire.work_nonces wire.c1_frontier
    wire.c2_frontier
    (Array.make 3#usize [v7_onefold.V7_COMPACT_BATCH_WORK_BITS,
      v7_onefold.V7_COMPACT_FOLD_WORK_BITS,
      v7_onefold.V7_COMPACT_FINAL_WORK_BITS])
    0#u8 v7_merkle208.V7_MERKLE_DIGEST_BYTES
    (transcript.label.V7_QUERY_BATCH_CHALLENGE,
      transcript.label.V7_QUERY_BATCH_CLAIM)
    false () inner.fields2 inactiveRowGroups inactiveGroupMasks checkPow
    inner.semanticPoint inner.pointClaims queryFold prechallenge captureSnapshot
    () verified returnedSnapshot onefoldSuccess
  obtain ⟨circle⟩ :=
    V7CallerCurrentReleaseR26AcceptedOuterLoop.AcceptedOnefoldLoopDispatch.exposesCircleLoop
      outer
  obtain ⟨origin⟩ :=
    V7CallerCurrentReleaseR26AcceptedCircleOrigin.AcceptedCircleLoopDispatch.exposesBodyOrigin
      circle
  obtain ⟨prechallengeDispatch⟩ :=
    V7CallerCurrentReleaseR26AcceptedPrechallengeDispatch.AcceptedCircleBodyOrigin.exposesPrechallengeDispatch
      origin
  exact ⟨{
    outer := outer
    circle := circle
    origin := origin
    prechallengeDispatch := prechallengeDispatch }⟩

/-- Direct capstone for the current generated shared-verifier body: acceptance
produces the full dependent dispatch chain to the literal post-prechallenge
call. -/
theorem accepted_inner_reaches_prechallenge_chain
    {TerminalCheck QueryFold Prechallenge : Type}
    (terminalInst : core.ops.function.FnOnce TerminalCheck
      v6_transcript.V6SemanticView Bool)
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (prechallengeInst : core.ops.function.FnMut Prechallenge
      v6_transcript.V6QueryBatchPrechallengeView Unit)
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (wire : v7_onefold.V7CompactOneFoldWire)
    (context : v6_transcript.V6TranscriptContext)
    (hidingContext : state_only_hiding.StateOnlyHidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16)
    (checkPow : Bool) (terminalCheck : TerminalCheck)
    (queryFold : QueryFold) (prechallenge : Prechallenge)
    (captureSnapshot : Bool)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option Snapshot)
    (success :
      v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner
        terminalInst queryFoldInst prechallengeInst hash wire context
        hidingContext inactiveRowGroups inactiveGroupMasks checkPow
        terminalCheck queryFold prechallenge captureSnapshot =
          ok (.Ok (verified, returnedSnapshot))) :
    Nonempty (Σ inner : AcceptedInnerDispatch terminalInst queryFoldInst
      prechallengeInst hash wire context hidingContext inactiveRowGroups
      inactiveGroupMasks checkPow terminalCheck queryFold prechallenge
      captureSnapshot verified returnedSnapshot,
      AcceptedInnerPrechallengeChain inner) := by
  obtain ⟨inner⟩ := accepted_inner_exposes_relation_dispatch terminalInst
    queryFoldInst prechallengeInst hash wire context hidingContext
    inactiveRowGroups inactiveGroupMasks checkPow terminalCheck queryFold
    prechallenge captureSnapshot verified returnedSnapshot success
  obtain ⟨chain⟩ :=
    V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge.AcceptedInnerDispatch.exposesPrechallengeChain
      inner
  exact ⟨⟨inner, chain⟩⟩

#print axioms AcceptedInnerDispatch.exposesPrechallengeChain
#print axioms accepted_inner_reaches_prechallenge_chain

end V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge
