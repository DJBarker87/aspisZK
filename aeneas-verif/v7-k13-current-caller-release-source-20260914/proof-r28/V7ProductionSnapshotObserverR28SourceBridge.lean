import V7ProductionSnapshotObserverR28.Funs

/-!
# Current production V7 snapshot-observer source bridge

This outer graph is extracted from the feature-gated production observer after
it was routed through the already generated R26 snapshot wrapper.  Shared
Aspis types are definitional aliases of the R26 generated types, so the core
call below is the concrete R26 source function rather than an external axiom.
-/

set_option autoImplicit false

namespace AspisV7ProductionSnapshotObserverR28SourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7ProductionSnapshotObserverR28

abbrev HashFn := Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)
abbrev Wire := aspis_core.v7_onefold.V7CompactOneFoldWire
abbrev Pubkey := solana_pubkey.Pubkey
abbrev Statement := aspis_statement.atomic_statement.AtomicPaymentStatementV4
abbrev HidingContext := aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev Transcript := aspis_core.v6_transcript.V6VerifiedTranscript
abbrev Snapshot := aspis_core.v6_transcript.V6QueryBatchPrechallengeSnapshot

noncomputable def snapshotCall
    (hash : HashFn) (wire : Wire)
    (programBytes releaseBinding statementDigest attemptBytes :
      Array Std.U8 32#usize)
    (hidingContext : HidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement) :
    Result (core.result.Result (Transcript × Option Snapshot)
      aspis_core.v6_transcript.V6TranscriptError) :=
  aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_snapshot
    v7_verifier.observe_v7_read_only_with_statement_digest.closure.Insts.CoreOpsFunctionFnOnceTupleSharedV6SemanticViewBool
    v7_verifier.observe_v7_read_only_with_statement_digest.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError
    hash wire
    { program_id := programBytes
      release_binding := releaseBinding
      statement_digest := statementDigest
      attempt_id := attemptBytes }
    hidingContext inactiveRowGroups inactiveGroupMasks checkPow statement
    (hash, wire)

/-- Successful exact interfaces force the current production snapshot observer
to return the same transcript and captured prechallenge snapshot. -/
theorem productionSnapshotObserver_success_exact
    (hash : HashFn) (proof : Slice Std.U8)
    (frontierNodes : Std.Usize) (programId : Pubkey)
    (releaseBinding : Array Std.U8 32#usize) (attemptId : Pubkey)
    (statement : Statement) (statementDigest : Array Std.U8 32#usize)
    (checkPow : Bool) (wire : Wire)
    (programBytes attemptBytes : Array Std.U8 32#usize)
    (hidingContext : HidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16)
    (transcript : Transcript) (snapshot : Snapshot)
    (parserSuccess :
      aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality
          proof frontierNodes = .ok (.Ok wire))
    (programBytesExact : solana_pubkey.Pubkey.to_bytes programId = .ok programBytes)
    (attemptBytesExact : solana_pubkey.Pubkey.to_bytes attemptId = .ok attemptBytes)
    (hidingContextExact :
      aspis_core.state_only_hiding.StateOnlyHidingContext.atomic_spend_v3
          statementDigest attemptBytes = .ok hidingContext)
    (rowScheduleExact :
      aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_v3 =
        .ok inactiveRowGroups)
    (maskScheduleExact :
      aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_v3 =
        .ok inactiveGroupMasks)
    (snapshotSuccess :
      snapshotCall hash wire programBytes releaseBinding statementDigest
          attemptBytes hidingContext inactiveRowGroups inactiveGroupMasks
          checkPow statement = .ok (.Ok (transcript, some snapshot))) :
    v7_verifier.observe_v7_read_only_with_statement_digest
        hash proof frontierNodes programId releaseBinding attemptId statement
        statementDigest checkPow =
      .ok (.Ok
        ({ transcript := transcript
           folded_query_sum := transcript.folded_query_sum }, snapshot)) := by
  unfold v7_verifier.observe_v7_read_only_with_statement_digest
  rw [parserSuccess]
  simp only [Bind.bind, Aeneas.Std.bind,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [programBytesExact]
  simp only
  rw [attemptBytesExact]
  simp only
  rw [hidingContextExact]
  simp only
  rw [rowScheduleExact]
  simp only
  rw [maskScheduleExact]
  simp only
  unfold snapshotCall at snapshotSuccess
  rw [snapshotSuccess]
  simp [Bind.bind, Aeneas.Std.bind,
    core.result.Result.Insts.CoreOpsTry.branch, core.option.Option.ok_or]

/-- Acceptance exposes the exact successful R26 snapshot-wrapper call and its
parser/context inputs. -/
theorem productionSnapshotObserver_acceptance_exposes_r26_snapshot
    (hash : HashFn) (proof : Slice Std.U8)
    (frontierNodes : Std.Usize) (programId : Pubkey)
    (releaseBinding : Array Std.U8 32#usize) (attemptId : Pubkey)
    (statement : Statement) (statementDigest : Array Std.U8 32#usize)
    (checkPow : Bool) (verified : v7_verifier.VerifiedV7ReadOnly)
    (snapshot : Snapshot)
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
      snapshotCall hash wire programBytes releaseBinding statementDigest
          attemptBytes hidingContext inactiveRowGroups inactiveGroupMasks
          checkPow statement = .ok (.Ok (transcript, some snapshot)) ∧
      verified =
        { transcript := transcript
          folded_query_sum := transcript.folded_query_sum } := by
  unfold v7_verifier.observe_v7_read_only_with_statement_digest at accepted
  generalize hparse :
      aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality
        proof frontierNodes = parseResult at accepted
  cases parseResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at accepted
  | div => simp [Bind.bind, Aeneas.Std.bind] at accepted
  | ok parsed =>
    cases parsed with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        v7_verifier.V7VerifyError.Insts.CoreConvertFromV6WireError.from,
        Bind.bind, Aeneas.Std.bind] at accepted
    | Ok wire =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
        at accepted
      generalize hprogram : solana_pubkey.Pubkey.to_bytes programId =
        programResult at accepted
      cases programResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at accepted
      | div => simp [Bind.bind, Aeneas.Std.bind] at accepted
      | ok programBytes =>
        simp only [bind_tc_ok] at accepted
        generalize hattempt : solana_pubkey.Pubkey.to_bytes attemptId =
          attemptResult at accepted
        cases attemptResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at accepted
        | div => simp [Bind.bind, Aeneas.Std.bind] at accepted
        | ok attemptBytes =>
          simp only [bind_tc_ok] at accepted
          generalize hhiding :
              aspis_core.state_only_hiding.StateOnlyHidingContext.atomic_spend_v3
                statementDigest attemptBytes = hidingResult at accepted
          cases hidingResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at accepted
          | div => simp [Bind.bind, Aeneas.Std.bind] at accepted
          | ok hidingContext =>
            simp only [bind_tc_ok] at accepted
            generalize hrows :
                aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_v3 =
                  rowsResult at accepted
            cases rowsResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at accepted
            | div => simp [Bind.bind, Aeneas.Std.bind] at accepted
            | ok inactiveRowGroups =>
              simp only [bind_tc_ok] at accepted
              generalize hmasks :
                  aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_v3 =
                    masksResult at accepted
              cases masksResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at accepted
              | div => simp [Bind.bind, Aeneas.Std.bind] at accepted
              | ok inactiveGroupMasks =>
                simp only [bind_tc_ok] at accepted
                generalize hcore :
                    aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_snapshot
                      v7_verifier.observe_v7_read_only_with_statement_digest.closure.Insts.CoreOpsFunctionFnOnceTupleSharedV6SemanticViewBool
                      v7_verifier.observe_v7_read_only_with_statement_digest.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError
                      hash wire
                      { program_id := programBytes
                        release_binding := releaseBinding
                        statement_digest := statementDigest
                        attempt_id := attemptBytes }
                      hidingContext inactiveRowGroups inactiveGroupMasks
                      checkPow statement (hash, wire) = coreResult at accepted
                cases coreResult with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at accepted
                | div => simp [Bind.bind, Aeneas.Std.bind] at accepted
                | ok inner =>
                  cases inner with
                  | Err error =>
                    simp [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      v7_verifier.V7VerifyError.Insts.CoreConvertFromV6TranscriptError.from,
                      Bind.bind, Aeneas.Std.bind] at accepted
                  | Ok pair =>
                    rcases pair with ⟨transcript, observed⟩
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,
                      bind_tc_ok] at accepted
                    cases observed with
                    | none =>
                      simp [core.option.Option.ok_or,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        Bind.bind, Aeneas.Std.bind] at accepted
                    | some observedSnapshot =>
                      simp [core.option.Option.ok_or,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        Bind.bind, Aeneas.Std.bind] at accepted
                      rcases accepted with ⟨rfl, rfl⟩
                      refine ⟨wire, programBytes, attemptBytes, hidingContext,
                        inactiveRowGroups, inactiveGroupMasks, transcript, rfl,
                        rfl, rfl, hhiding, rfl, rfl, ?_, rfl⟩
                      unfold snapshotCall
                      exact hcore

#print axioms productionSnapshotObserver_success_exact
#print axioms productionSnapshotObserver_acceptance_exposes_r26_snapshot

end AspisV7ProductionSnapshotObserverR28SourceBridge
