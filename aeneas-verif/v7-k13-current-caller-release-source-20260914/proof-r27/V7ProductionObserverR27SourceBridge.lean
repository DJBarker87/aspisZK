import V7ProductionObserverR27.Funs

/-!
# Current production V7 observer source bridge

The generated module is extracted from
`observe_v7_read_only_with_statement_digest` at source revision
`fd8ca3a715c234a46c2c436fa92eb05eb9ff0713`.  The observer uses the same
parser, context construction, terminal callback, authenticated query callback,
and shared verifier as the production read-only verifier, while returning the
captured state immediately before the query-batch challenge.

This bridge records the exact result flow through those generated interfaces.
It does not assume that any opaque interface is semantically correct; those
interfaces remain explicit obligations for the end-to-end composition.
-/

set_option autoImplicit false

namespace AspisV7ProductionObserverR27SourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7ProductionObserverR27Outer

abbrev HashFn :=
  Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)
abbrev Wire := aspis_core.v7_onefold.V7CompactOneFoldWire
abbrev Pubkey := solana_pubkey.Pubkey
abbrev Statement :=
  aspis_statement.atomic_statement.AtomicPaymentStatementV4
abbrev HidingContext :=
  aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev Transcript := aspis_core.v6_transcript.V6VerifiedTranscript
abbrev Snapshot :=
  aspis_core.v6_transcript.V6QueryBatchPrechallengeSnapshot

noncomputable def observerCall
    (hash : HashFn) (wire : Wire)
    (programBytes releaseBinding statementDigest attemptBytes :
      Array Std.U8 32#usize)
    (hidingContext : HidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement) :
    Result ((core.result.Result Transcript
      aspis_core.v6_transcript.V6TranscriptError) ×
      Option Snapshot) :=
  aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_observe
    v7_verifier.observe_v7_read_only_with_statement_digest.closure.Insts.CoreOpsFunctionFnOnceTupleSharedV6SemanticViewBool
    v7_verifier.observe_v7_read_only_with_statement_digest.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError
    v7_verifier.observe_v7_read_only_with_statement_digest.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedV6QueryBatchPrechallengeViewTuple
    hash wire
    { program_id := programBytes
      release_binding := releaseBinding
      statement_digest := statementDigest
      attempt_id := attemptBytes }
    hidingContext inactiveRowGroups inactiveGroupMasks checkPow statement
    (hash, wire) none

/-- Successful exact generated interfaces force the current production
observer entry to return the same transcript and captured prechallenge
snapshot. -/
theorem productionObserver_success_exact
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
    (programBytesExact :
      solana_pubkey.Pubkey.to_bytes programId = .ok programBytes)
    (attemptBytesExact :
      solana_pubkey.Pubkey.to_bytes attemptId = .ok attemptBytes)
    (hidingContextExact :
      aspis_core.state_only_hiding.StateOnlyHidingContext.atomic_spend_v3
          statementDigest attemptBytes = .ok hidingContext)
    (rowScheduleExact :
      aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_v3 =
        .ok inactiveRowGroups)
    (maskScheduleExact :
      aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_v3 =
        .ok inactiveGroupMasks)
    (observerSuccess :
      observerCall hash wire programBytes releaseBinding statementDigest
          attemptBytes hidingContext inactiveRowGroups inactiveGroupMasks
          checkPow statement =
        .ok (.Ok transcript, some snapshot)) :
    v7_verifier.observe_v7_read_only_with_statement_digest
        hash proof frontierNodes programId releaseBinding attemptId statement
        statementDigest checkPow =
      .ok (.Ok
        ({ transcript := transcript
           folded_query_sum := transcript.folded_query_sum },
         snapshot)) := by
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
  unfold observerCall at observerSuccess
  rw [observerSuccess]
  simp [Bind.bind, Aeneas.Std.bind,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.option.Option.ok_or]

/-- An exact parser rejection is propagated as a query error, so the current
entry has no parser-bypass acceptance path. -/
theorem productionObserver_parser_rejection_is_fail_closed
    (hash : HashFn) (proof : Slice Std.U8)
    (frontierNodes : Std.Usize) (programId : Pubkey)
    (releaseBinding : Array Std.U8 32#usize) (attemptId : Pubkey)
    (statement : Statement) (statementDigest : Array Std.U8 32#usize)
    (checkPow : Bool) (wireError : aspis_core.v6_onefold.V6WireError)
    (parserRejects :
      aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality
          proof frontierNodes = .ok (.Err wireError)) :
    v7_verifier.observe_v7_read_only_with_statement_digest
        hash proof frontierNodes programId releaseBinding attemptId statement
        statementDigest checkPow =
      .ok (.Err (.Query wireError)) := by
  simp [v7_verifier.observe_v7_read_only_with_statement_digest,
    parserRejects, Bind.bind, Aeneas.Std.bind,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    v7_verifier.V7VerifyError.Insts.CoreConvertFromV6WireError.from]

/-- Acceptance by the current production observer exposes one successful
parse, exact context construction, frozen schedule reads, and one successful
shared-core execution returning the observed prechallenge snapshot. -/
theorem productionObserver_acceptance_exposes_core
    (hash : HashFn) (proof : Slice Std.U8)
    (frontierNodes : Std.Usize) (programId : Pubkey)
    (releaseBinding : Array Std.U8 32#usize) (attemptId : Pubkey)
    (statement : Statement) (statementDigest : Array Std.U8 32#usize)
    (checkPow : Bool) (verified : v7_verifier.VerifiedV7ReadOnly)
    (snapshot : Snapshot)
    (accepted :
      v7_verifier.observe_v7_read_only_with_statement_digest
          hash proof frontierNodes programId releaseBinding attemptId statement
          statementDigest checkPow =
        .ok (.Ok (verified, snapshot))) :
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
      observerCall hash wire programBytes releaseBinding statementDigest
          attemptBytes hidingContext inactiveRowGroups inactiveGroupMasks
          checkPow statement =
        .ok (.Ok transcript, some snapshot) ∧
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
      generalize hprogram :
          solana_pubkey.Pubkey.to_bytes programId = programResult at accepted
      cases programResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at accepted
      | div => simp [Bind.bind, Aeneas.Std.bind] at accepted
      | ok programBytes =>
        simp only [bind_tc_ok] at accepted
        generalize hattempt :
            solana_pubkey.Pubkey.to_bytes attemptId = attemptResult at accepted
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
                    aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_observe
                      v7_verifier.observe_v7_read_only_with_statement_digest.closure.Insts.CoreOpsFunctionFnOnceTupleSharedV6SemanticViewBool
                      v7_verifier.observe_v7_read_only_with_statement_digest.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError
                      v7_verifier.observe_v7_read_only_with_statement_digest.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedV6QueryBatchPrechallengeViewTuple
                      hash wire
                      { program_id := programBytes
                        release_binding := releaseBinding
                        statement_digest := statementDigest
                        attempt_id := attemptBytes }
                      hidingContext inactiveRowGroups inactiveGroupMasks
                      checkPow statement (hash, wire) none =
                    coreResult at accepted
                cases coreResult with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at accepted
                | div => simp [Bind.bind, Aeneas.Std.bind] at accepted
                | ok corePair =>
                  rcases corePair with ⟨inner, observed⟩
                  cases inner with
                  | Err error =>
                    simp [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      v7_verifier.V7VerifyError.Insts.CoreConvertFromV6TranscriptError.from,
                      Bind.bind, Aeneas.Std.bind] at accepted
                  | Ok transcript =>
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
                      unfold observerCall
                      exact hcore

#print axioms productionObserver_success_exact
#print axioms productionObserver_parser_rejection_is_fail_closed
#print axioms productionObserver_acceptance_exposes_core

end AspisV7ProductionObserverR27SourceBridge
