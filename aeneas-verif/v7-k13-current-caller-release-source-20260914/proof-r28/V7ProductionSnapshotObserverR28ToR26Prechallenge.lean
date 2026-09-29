import V7ProductionSnapshotObserverR28SourceBridge
import V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge

/-!
# Accepted production snapshot observer reaches the R26 prechallenge chain

The R28 outer entry and the R26 shared verifier use definitionally identical
generated core types.  This module unfolds the concrete snapshot wrapper and
feeds its successful inner call to the existing R26 accepted-path inversion.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace AspisV7ProductionSnapshotObserverR28ToR26Prechallenge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7ProductionSnapshotObserverR28
open AspisV7ProductionSnapshotObserverR28SourceBridge
open V7CallerCurrentReleaseR26AcceptedInnerDispatch
open V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge

abbrev QueryFold :=
  v7_verifier.observe_v7_read_only_with_statement_digest.closure_1
abbrev Prechallenge :=
  V7CallerCurrentReleaseR26.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_snapshot.closure
    Statement QueryFold

noncomputable abbrev terminalInst : core.ops.function.FnOnce Statement
    V7CallerCurrentReleaseR26.v6_transcript.V6SemanticView Bool :=
  v7_verifier.observe_v7_read_only_with_statement_digest.closure.Insts.CoreOpsFunctionFnOnceTupleSharedV6SemanticViewBool

noncomputable abbrev queryFoldInst : core.ops.function.FnOnce QueryFold
    V7CallerCurrentReleaseR26.v6_transcript.V6QueryBatchView
    (core.result.Result
      V7CallerCurrentReleaseR26.v6_query_batch.V6AuthenticatedQueryBatch
      V7CallerCurrentReleaseR26.v6_onefold.V6WireError) :=
  v7_verifier.observe_v7_read_only_with_statement_digest.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError

noncomputable abbrev prechallengeInst : core.ops.function.FnMut Prechallenge
    V7CallerCurrentReleaseR26.v6_transcript.V6QueryBatchPrechallengeView Unit :=
  V7CallerCurrentReleaseR26.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_snapshot.closure.Insts.CoreOpsFunctionFnMutTupleSharedV6QueryBatchPrechallengeViewTuple
    terminalInst queryFoldInst

/-- The exact dependent witness furnished by the R26 accepted inner path. -/
def ReachesR26Prechallenge
    (hash : HashFn) (wire : Wire)
    (context : V7CallerCurrentReleaseR26.v6_transcript.V6TranscriptContext)
    (hidingContext : HidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement) (queryFold : QueryFold)
    (transcript : Transcript)
    (snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot) : Prop :=
  Nonempty (Σ inner : AcceptedInnerDispatch terminalInst queryFoldInst
      prechallengeInst hash wire context hidingContext inactiveRowGroups
      inactiveGroupMasks checkPow statement queryFold () true transcript
      (some snapshot),
    AcceptedInnerPrechallengeChain inner)

/-- A successful concrete R28 snapshot call unfolds to the literal R26 inner
call and therefore reaches the already proved prechallenge dispatch chain. -/
theorem snapshot_success_reaches_r26_prechallenge
    (hash : HashFn) (wire : Wire)
    (programBytes releaseBinding statementDigest attemptBytes :
      Array Std.U8 32#usize)
    (hidingContext : HidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement) (transcript : Transcript)
    (snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot)
    (success :
      snapshotCall hash wire programBytes releaseBinding statementDigest
          attemptBytes hidingContext inactiveRowGroups inactiveGroupMasks
          checkPow statement = .ok (.Ok (transcript, some snapshot))) :
    ReachesR26Prechallenge hash wire
      { program_id := programBytes
        release_binding := releaseBinding
        statement_digest := statementDigest
        attempt_id := attemptBytes }
      hidingContext inactiveRowGroups inactiveGroupMasks checkPow statement
      (hash, wire) transcript snapshot := by
  unfold snapshotCall at success
  unfold aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_snapshot at success
  unfold V7CallerCurrentReleaseR26.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_snapshot at success
  exact V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge.accepted_inner_reaches_prechallenge_chain
    terminalInst queryFoldInst prechallengeInst hash wire
    { program_id := programBytes
      release_binding := releaseBinding
      statement_digest := statementDigest
      attempt_id := attemptBytes }
    hidingContext inactiveRowGroups inactiveGroupMasks checkPow statement
    (hash, wire) () true transcript (some snapshot) success

#print axioms snapshot_success_reaches_r26_prechallenge

/-- Acceptance by the proof-only production observer exposes both the exact
parser result and an R26 accepted-path witness reaching the post-prechallenge
call.  The observer is generated from the current production entry and calls
the same shared verifier body as the default-feature path. -/
theorem production_snapshot_observer_acceptance_reaches_r26_prechallenge
    (hash : HashFn) (proof : Slice Std.U8)
    (frontierNodes : Std.Usize) (programId : Pubkey)
    (releaseBinding : Array Std.U8 32#usize) (attemptId : Pubkey)
    (statement : Statement) (statementDigest : Array Std.U8 32#usize)
    (checkPow : Bool) (verified : v7_verifier.VerifiedV7ReadOnly)
    (snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot)
    (accepted :
      v7_verifier.observe_v7_read_only_with_statement_digest
          hash proof frontierNodes programId releaseBinding attemptId statement
          statementDigest checkPow = .ok (.Ok (verified, snapshot))) :
    ∃ (wire : Wire) (programBytes attemptBytes : Array Std.U8 32#usize)
      (hidingContext : HidingContext)
      (inactiveRowGroups : Array Std.U8 64#usize)
      (inactiveGroupMasks : Slice Std.U16) (transcript : Transcript),
      aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality
          proof frontierNodes = .ok (.Ok wire) ∧
      solana_pubkey.Pubkey.to_bytes programId = .ok programBytes ∧
      solana_pubkey.Pubkey.to_bytes attemptId = .ok attemptBytes ∧
      aspis_core.state_only_hiding.StateOnlyHidingContext.atomic_spend_v3
          statementDigest attemptBytes = .ok hidingContext ∧
      aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_v3 =
        .ok inactiveRowGroups ∧
      aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_v3 =
        .ok inactiveGroupMasks ∧
      ReachesR26Prechallenge hash wire
        { program_id := programBytes
          release_binding := releaseBinding
          statement_digest := statementDigest
          attempt_id := attemptBytes }
        hidingContext inactiveRowGroups inactiveGroupMasks checkPow statement
        (hash, wire) transcript snapshot ∧
      verified =
        { transcript := transcript
          folded_query_sum := transcript.folded_query_sum } := by
  rcases productionSnapshotObserver_acceptance_exposes_r26_snapshot
      hash proof frontierNodes programId releaseBinding attemptId statement
      statementDigest checkPow verified snapshot accepted with
    ⟨wire, programBytes, attemptBytes, hidingContext, inactiveRowGroups,
      inactiveGroupMasks, transcript, hparse, hprogram, hattempt, hhiding,
      hrows, hmasks, hsnapshot, hvertified⟩
  refine ⟨wire, programBytes, attemptBytes, hidingContext, inactiveRowGroups,
    inactiveGroupMasks, transcript, hparse, hprogram, hattempt, hhiding,
    hrows, hmasks, ?_, hvertified⟩
  exact snapshot_success_reaches_r26_prechallenge hash wire programBytes
    releaseBinding statementDigest attemptBytes hidingContext inactiveRowGroups
    inactiveGroupMasks checkPow statement transcript snapshot hsnapshot

#print axioms production_snapshot_observer_acceptance_reaches_r26_prechallenge

end AspisV7ProductionSnapshotObserverR28ToR26Prechallenge
