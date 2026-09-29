import V7CallerCurrentReleaseR26AcceptedTerminalEndToEnd

/-!
# Successful full inner verifier reaches the literal relation call

This module inverts the translated shared V7 verifier body through fixed-field
reader construction, transcript initialization, the compact semantic rounds,
point-claim decoding, and the terminal callback.  The resulting witness keeps
the exact `finish_v7_compact_relation` call from the same successful source
execution.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedInnerDispatch

abbrev RawQM31 := field.QM31
abbrev Snapshot := v6_transcript.V6QueryBatchPrechallengeSnapshot

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    Bind.bind input next = .ok output ↔
      ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem branch_eq_ok_of_continue {Value Error : Type}
    (result : core.result.Result Value Error) (value : Value)
    (success : core.result.Result.Insts.CoreOpsTry.branch result =
      .ok (.Continue value)) :
    result = .Ok value := by
  cases result with
  | Ok actual =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch] using success
  | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at success

/-- Exact successful prefix and dispatch facts exposed by the generated shared
inner verifier. -/
structure AcceptedInnerDispatch
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
    (returnedSnapshot : Option Snapshot) : Type where
  fields0 : v6_onefold.V6FixedFieldReader
  fields0Run : v6_onefold.V6FixedFieldReader.impl.new
      wire.fixed_fields_packed = ok (.Ok fields0)
  transcript0 : transcript.Transcript
  lambda : RawQM31
  chi : RawQM31
  batching : statement_sumcheck.PaymentConstraintChallenges
  beginRun :
    v6_transcript.begin_v7_compact_transcript_with_hiding_context hash context
      wire hidingContext = ok (.Ok (transcript0, lambda, chi, batching))
  eta : RawQM31
  semanticPoint : Array RawQM31 10#usize
  semanticTerminal : RawQM31
  transcript1 : transcript.Transcript
  fields1 : v6_onefold.V6FixedFieldReader
  semanticRun :
    v6_transcript.verify_compact_semantic_sumcheck
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
      transcript0 fields0 =
        ok (.Ok (eta, semanticPoint, semanticTerminal), transcript1, fields1)
  pointClaims : Array (Array RawQM31 29#usize) 3#usize
  transcript2 : transcript.Transcript
  fields2 : v6_onefold.V6FixedFieldReader
  pointClaimsRun :
    v6_transcript.decode_and_absorb_point_claims
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
      transcript1 fields1 = ok (.Ok pointClaims, transcript2, fields2)
  terminalAccepted : terminalInst.call_once terminalCheck
      { lambda := lambda
        chi := chi
        batching := batching
        eta := eta
        point := semanticPoint
        terminal_claim := semanticTerminal
        point_claims := pointClaims } = ok true
  relationSuccess :
    v6_transcript.finish_v7_compact_relation queryFoldInst
      (v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple
        terminalInst queryFoldInst prechallengeInst)
      prechallengeInst transcript2 wire fields2 inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint pointClaims queryFold
      prechallenge captureSnapshot () =
        ok (.Ok (verified, returnedSnapshot))

/-- Any successful result of the literal generated shared verifier body carries
one `AcceptedInnerDispatch`. No parser, transcript, terminal, or relation call
is replaced by a model premise. -/
theorem accepted_inner_exposes_relation_dispatch
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
    Nonempty (AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow terminalCheck queryFold prechallenge captureSnapshot verified
      returnedSnapshot) := by
  unfold v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨readerResult, readerRun, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨readerFlow, readerBranch, success⟩ := success
  cases readerFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          cases converted :
              v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from
                error <;>
            simp [converted,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
              at success
  | Continue fields0 =>
      have fields0Exact := branch_eq_ok_of_continue readerResult fields0
        readerBranch
      rw [fields0Exact] at readerRun
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨beginResult, beginRun, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨beginFlow, beginBranch, success⟩ := success
      cases beginFlow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at success
      | Continue beginValues =>
          rcases beginValues with ⟨transcript0, lambda, chi, batching⟩
          have beginExact := branch_eq_ok_of_continue beginResult
            (transcript0, lambda, chi, batching) beginBranch
          rw [beginExact] at beginRun
          simp only at success
          rw [bind_eq_ok_iff] at success
          obtain ⟨semanticValues, semanticRun, success⟩ := success
          rcases semanticValues with ⟨semanticResult, transcript1, fields1⟩
          rw [bind_eq_ok_iff] at success
          obtain ⟨semanticFlow, semanticBranch, success⟩ := success
          cases semanticFlow with
          | Break residual =>
              cases residual with
              | Ok impossible => nomatch impossible
              | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at success
          | Continue semanticValues =>
              rcases semanticValues with ⟨eta, semanticPoint, semanticTerminal⟩
              have semanticExact := branch_eq_ok_of_continue semanticResult
                (eta, semanticPoint, semanticTerminal) semanticBranch
              rw [semanticExact] at semanticRun
              simp only at success
              rw [bind_eq_ok_iff] at success
              obtain ⟨claimValues, pointClaimsRun, success⟩ := success
              rcases claimValues with ⟨claimResult, transcript2, fields2⟩
              rw [bind_eq_ok_iff] at success
              obtain ⟨claimFlow, claimBranch, success⟩ := success
              cases claimFlow with
              | Break residual =>
                  cases residual with
                  | Ok impossible => nomatch impossible
                  | Err error =>
                      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from] at success
              | Continue pointClaims =>
                  have claimsExact := branch_eq_ok_of_continue claimResult
                    pointClaims claimBranch
                  rw [claimsExact] at pointClaimsRun
                  simp only at success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨terminalResult, terminalRun, success⟩ := success
                  cases terminalResult with
                  | false => simp at success
                  | true =>
                      simp only [↓reduceIte] at success
                      exact ⟨{
                        fields0 := fields0
                        fields0Run := readerRun
                        transcript0 := transcript0
                        lambda := lambda
                        chi := chi
                        batching := batching
                        beginRun := beginRun
                        eta := eta
                        semanticPoint := semanticPoint
                        semanticTerminal := semanticTerminal
                        transcript1 := transcript1
                        fields1 := fields1
                        semanticRun := semanticRun
                        pointClaims := pointClaims
                        transcript2 := transcript2
                        fields2 := fields2
                        pointClaimsRun := pointClaimsRun
                        terminalAccepted := terminalRun
                        relationSuccess := success }⟩

/-- The dispatch witness exposes the literal `finish_onefold_relation` call
used by the compact V7 specialization. -/
theorem AcceptedInnerDispatch.finishOnefoldSuccess
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
    (dispatch : AcceptedInnerDispatch terminalInst queryFoldInst
      prechallengeInst hash wire context hidingContext inactiveRowGroups
      inactiveGroupMasks checkPow terminalCheck queryFold prechallenge
      captureSnapshot verified returnedSnapshot) :
    v6_transcript.finish_onefold_relation queryFoldInst
      (v6_transcript.finish_v7_compact_relation.closure.Insts.CoreOpsFunctionFnOnceTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptError
        queryFoldInst
        (v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple
          terminalInst queryFoldInst prechallengeInst)
        prechallengeInst)
      (v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple
        terminalInst queryFoldInst prechallengeInst)
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
      prechallengeInst dispatch.transcript2 wire.work_nonces wire.c1_frontier
      wire.c2_frontier
      (Array.make 3#usize [v7_onefold.V7_COMPACT_BATCH_WORK_BITS,
        v7_onefold.V7_COMPACT_FOLD_WORK_BITS,
        v7_onefold.V7_COMPACT_FINAL_WORK_BITS])
      0#u8 v7_merkle208.V7_MERKLE_DIGEST_BYTES
      (transcript.label.V7_QUERY_BATCH_CHALLENGE,
        transcript.label.V7_QUERY_BATCH_CLAIM)
      true false () dispatch.fields2 inactiveRowGroups inactiveGroupMasks
      checkPow dispatch.semanticPoint dispatch.pointClaims queryFold prechallenge
      captureSnapshot () = ok (.Ok (verified, returnedSnapshot)) := by
  simpa [v6_transcript.finish_v7_compact_relation] using
    dispatch.relationSuccess

#print axioms accepted_inner_exposes_relation_dispatch
#print axioms AcceptedInnerDispatch.finishOnefoldSuccess

end V7CallerCurrentReleaseR26AcceptedInnerDispatch
