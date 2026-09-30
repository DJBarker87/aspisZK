import V7ProductionSnapshotObserverR28ToR26Prechallenge
import V7CallerCurrentReleaseR26AcceptedPrechallengeComposition
import V7CallerCurrentReleaseR26AcceptedTailComposition

/-!
# Accepted production snapshot observer reaches the relation tail

This module composes the production-entry witness with the R26
post-prechallenge inversion.  It retains the exact shifted-query insertion,
the literal accepted relation-loop call, and the equality showing that the
returned capture is the snapshot supplied by the production observer.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace AspisV7ProductionSnapshotObserverR28AcceptedTail

open Aeneas Aeneas.Std Result ControlFlow Error
open V7ProductionSnapshotObserverR28
open AspisV7ProductionSnapshotObserverR28SourceBridge
open AspisV7ProductionSnapshotObserverR28ToR26Prechallenge
open V7CallerCurrentReleaseR26
open V7CallerCurrentReleaseR26AcceptedInnerDispatch
open V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge
open V7CallerCurrentReleaseR26AcceptedTailDispatch
open V7CallerCurrentReleaseR26AcceptedPrechallengeComposition
open V7CallerCurrentReleaseR26AcceptedTailComposition

noncomputable abbrev traceInst : core.ops.function.FnMut Unit
    V7CallerCurrentReleaseR26.v6_transcript.V6RelationDiagnosticPhase Unit :=
  V7CallerCurrentReleaseR26.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple
    terminalInst queryFoldInst prechallengeInst

/-- The accepted relation-tail witness carried by one complete production
snapshot execution. -/
structure AcceptedProductionTail
    {hash : HashFn} {wire : Wire}
    {context : V7CallerCurrentReleaseR26.v6_transcript.V6TranscriptContext}
    {hidingContext : HidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {statement : Statement} {queryFold : QueryFold}
    {transcript : Transcript}
    {snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot}
    (inner : AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement queryFold () true transcript (some snapshot))
    (chain : AcceptedInnerPrechallengeChain inner) : Type where
  tail : AcceptedShiftedTailDispatch queryFoldInst queryFold traceInst
    chain.outer.gamma chain.prechallengeDispatch.relationFields 0#u8
    inner.semanticPoint chain.outer.kappa chain.prechallengeDispatch.queries
    chain.prechallengeDispatch.compactCounter
    chain.prechallengeDispatch.frontierNodes
    chain.prechallengeDispatch.transcriptStateAfterQueries
    chain.prechallengeDispatch.prechallengeSnapshot
    chain.prechallengeDispatch.alpha chain.prechallengeDispatch.foldedValues
    chain.prechallengeDispatch.weights chain.prechallengeDispatch.runningClaim
    transcript (some snapshot) chain.prechallengeDispatch.traceAfterPrechallenge
  source : AcceptedTailSourceTrace chain.outer.gamma
    chain.prechallengeDispatch.relationFields 0#u8 inner.semanticPoint
    chain.outer.kappa chain.prechallengeDispatch.queries
    chain.prechallengeDispatch.compactCounter
    chain.prechallengeDispatch.frontierNodes
    chain.prechallengeDispatch.transcriptStateAfterQueries
    chain.prechallengeDispatch.prechallengeSnapshot tail.queryBatchChallenge
    tail.authenticatedQueries tail.transcriptAfterClaim tail.traceAfterClaim
    tail.runningClaimAfter tail.weightsAfter chain.prechallengeDispatch.alpha
    chain.prechallengeDispatch.foldedValues transcript (some snapshot)
    chain.prechallengeDispatch.traceAfterPrechallenge
  snapshotExact :
    chain.prechallengeDispatch.prechallengeSnapshot = some snapshot

/-- The dependent accepted-tail witness exposed by the current production
snapshot observer. -/
def ReachesR26AcceptedTail
    (hash : HashFn) (wire : Wire)
    (context : V7CallerCurrentReleaseR26.v6_transcript.V6TranscriptContext)
    (hidingContext : HidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement) (queryFold : QueryFold)
    (transcript : Transcript)
    (snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot) :
    Prop :=
  Nonempty (Σ inner : AcceptedInnerDispatch terminalInst queryFoldInst
      prechallengeInst hash wire context hidingContext inactiveRowGroups
      inactiveGroupMasks checkPow statement queryFold () true transcript
      (some snapshot),
    Σ chain : AcceptedInnerPrechallengeChain inner,
      AcceptedProductionTail inner chain)

/-- Reaching the R26 prechallenge chain is enough to reach its literal
accepted relation tail, with no additional premise. -/
theorem reaches_r26_prechallenge_reaches_accepted_tail
    (hash : HashFn) (wire : Wire)
    (context : V7CallerCurrentReleaseR26.v6_transcript.V6TranscriptContext)
    (hidingContext : HidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement) (queryFold : QueryFold)
    (transcript : Transcript)
    (snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot)
    (reaches : ReachesR26Prechallenge hash wire context hidingContext
      inactiveRowGroups inactiveGroupMasks checkPow statement queryFold
      transcript snapshot) :
    ReachesR26AcceptedTail hash wire context hidingContext inactiveRowGroups
      inactiveGroupMasks checkPow statement queryFold transcript snapshot := by
  rcases reaches with ⟨⟨inner, chain⟩⟩
  let dispatch := chain.prechallengeDispatch
  obtain ⟨snapshotReturned, tail⟩ :=
    accepted_after_prechallenge_returns_supplied_snapshot queryFoldInst
      traceInst dispatch.acceptedQueryTranscript wire.c1_frontier
      wire.c2_frontier v7_merkle208.V7_MERKLE_DIGEST_BYTES
      (V7CallerCurrentReleaseR26.transcript.label.V7_QUERY_BATCH_CHALLENGE,
        V7CallerCurrentReleaseR26.transcript.label.V7_QUERY_BATCH_CLAIM)
      false queryFold dispatch.traceAfterFinal chain.outer.gamma
      chain.outer.gammaPowers chain.outer.dPower dispatch.runningClaim
      dispatch.weights dispatch.alpha dispatch.foldedValues
      dispatch.relationFields 0#u8 inner.semanticPoint chain.outer.kappa
      dispatch.queries dispatch.compactCounter dispatch.frontierNodes
      dispatch.transcriptStateAfterQueries dispatch.prechallengeSnapshot
      transcript (some snapshot) dispatch.traceAfterPrechallenge
      dispatch.success
  rcases tail with ⟨tail⟩
  obtain ⟨source⟩ := accepted_relation_loop_exposes_source_trace
    queryFoldInst traceInst tail.transcriptAfterClaim tail.traceAfterClaim
    chain.outer.gamma tail.runningClaimAfter tail.weightsAfter
    dispatch.alpha dispatch.foldedValues dispatch.relationFields 0#u8
    inner.semanticPoint chain.outer.kappa dispatch.queries
    dispatch.compactCounter dispatch.frontierNodes
    dispatch.transcriptStateAfterQueries dispatch.prechallengeSnapshot
    tail.queryBatchChallenge tail.authenticatedQueries transcript
    (some snapshot) dispatch.traceAfterPrechallenge tail.tailSuccess
  exact ⟨⟨inner, chain, {
    tail := tail
    source := source
    snapshotExact := snapshotReturned.symm }⟩⟩

#print axioms reaches_r26_prechallenge_reaches_accepted_tail

/-- Acceptance by the current proof-only production observer reaches the
literal accepted relation tail while retaining the exact parser and context
results used by that same execution. -/
theorem production_snapshot_observer_acceptance_reaches_accepted_tail
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
      ReachesR26AcceptedTail hash wire
        { program_id := programBytes
          release_binding := releaseBinding
          statement_digest := statementDigest
          attempt_id := attemptBytes }
        hidingContext inactiveRowGroups inactiveGroupMasks checkPow statement
        (hash, wire) transcript snapshot ∧
      verified =
        { transcript := transcript
          folded_query_sum := transcript.folded_query_sum } := by
  rcases production_snapshot_observer_acceptance_reaches_r26_prechallenge
      hash proof frontierNodes programId releaseBinding attemptId statement
      statementDigest checkPow verified snapshot accepted with
    ⟨wire, programBytes, attemptBytes, hidingContext, inactiveRowGroups,
      inactiveGroupMasks, transcript, hparse, hprogram, hattempt, hhiding,
      hrows, hmasks, reaches, hvertified⟩
  exact ⟨wire, programBytes, attemptBytes, hidingContext, inactiveRowGroups,
    inactiveGroupMasks, transcript, hparse, hprogram, hattempt, hhiding,
    hrows, hmasks,
    reaches_r26_prechallenge_reaches_accepted_tail hash wire
      { program_id := programBytes
        release_binding := releaseBinding
        statement_digest := statementDigest
        attempt_id := attemptBytes }
      hidingContext inactiveRowGroups inactiveGroupMasks checkPow statement
      (hash, wire) transcript snapshot reaches,
    hvertified⟩

#print axioms production_snapshot_observer_acceptance_reaches_accepted_tail

end AspisV7ProductionSnapshotObserverR28AcceptedTail
