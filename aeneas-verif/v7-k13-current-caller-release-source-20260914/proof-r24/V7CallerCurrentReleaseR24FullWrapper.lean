import V7CallerCurrentReleaseR24.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR24

namespace V7CallerCurrentReleaseR24FullWrapper

open V7CallerCurrentReleaseR24

/-- The complete observer snapshot wrapper is definitionally the production
inner verifier with its generated no-op prechallenge callback and capture set
to `true`. This retains the actual parser, transcript, terminal, relation, and
query path; it introduces no observer result or acceptance assumption. -/
theorem snapshot_wrapper_calls_captured_inner
    {TerminalCheck QueryFold : Type}
    (terminalInst :
      core.ops.function.FnOnce TerminalCheck v6_transcript.V6SemanticView Bool)
    (queryInst :
      core.ops.function.FnOnce QueryFold v6_transcript.V6QueryBatchView
        (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
          v6_onefold.V6WireError))
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (wire : v7_onefold.V7CompactOneFoldWire)
    (context : v6_transcript.V6TranscriptContext)
    (hidingContext : state_only_hiding.StateOnlyHidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16)
    (checkPow : Bool)
    (terminalCheck : TerminalCheck)
    (queryFold : QueryFold) :
    v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_snapshot
      terminalInst queryInst hash wire context hidingContext inactiveRowGroups
      inactiveGroupMasks checkPow terminalCheck queryFold =
    v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner
      terminalInst queryInst
      (v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_snapshot.closure.Insts.CoreOpsFunctionFnMutTupleSharedV6QueryBatchPrechallengeViewTuple
        terminalInst queryInst)
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow terminalCheck queryFold () true := by
  rfl

#print axioms snapshot_wrapper_calls_captured_inner

end V7CallerCurrentReleaseR24FullWrapper
