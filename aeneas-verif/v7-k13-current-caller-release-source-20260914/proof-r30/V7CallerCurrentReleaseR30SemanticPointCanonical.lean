import V7CallerCurrentReleaseR30ChallengeCanonical

/-!
# Canonicality of the compact semantic sumcheck point

The semantic verifier starts from the all-zero ten-coordinate point.  Each
successful round stores one ordinary transcript challenge in that point.  This
module follows the two generated fixpoints symbolically and proves that every
point returned by a successful semantic verifier call is canonical.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30SemanticPointCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR30ChallengeCanonical

abbrev RawQM31 := field.QM31
abbrev Point := Array RawQM31 10#usize

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def CanonicalPoint (point : Point) : Prop :=
  ∀ index, index < 10 → GeneratedCanonicalQM31 point.val[index]!

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem branch_eq_ok_of_continue {Value Error : Type}
    (result : core.result.Result Value Error) (value : Value)
    (success : core.result.Result.Insts.CoreOpsTry.branch result =
      ok (.Continue value)) :
    result = .Ok value := by
  cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at success ⊢
  exact success

private theorem canonical_point_update
    (point next : Point) (index : Std.Usize) (value : RawQM31)
    (run : Array.update point index value = ok next)
    (canonical : CanonicalPoint point)
    (valueCanonical : GeneratedCanonicalQM31 value) :
    CanonicalPoint next := by
  have updateFacts : index.val < 10 ∧ next = point.set index value := by
    unfold Array.update at run
    split at run
    · cases run
    · rename_i present
      have presentSome : (point.val[index.val]?).isSome := by
        simpa using congrArg Option.isSome present
      have indexBound : index.val < point.val.length := by
        by_contra outOfBounds
        have absent : point.val[index.val]? = none := by
          exact List.getElem?_eq_none (by omega)
        rw [absent] at presentSome
        cases presentSome
      exact ⟨by simpa [Array.length_eq] using indexBound,
        (Result.ok.inj run).symm⟩
  rw [updateFacts.2]
  unfold CanonicalPoint
  intro target targetBound
  by_cases same : target = index.val
  · subst target
    rw [Array.set_val_eq]
    rw [List.set_getElem!_eq _ _ _ _ ⟨by
      simpa [Array.length_eq] using updateFacts.1, rfl⟩]
    exact valueCanonical
  · rw [Array.set_val_eq]
    rw [List.set_getElem!_ne _ _ _ _ (by omega)]
    exact canonical target targetBound

abbrev InnerState (Fields : Type) :=
  core.ops.range.Range Std.Usize × Fields ×
    Array RawQM31 28#usize × Array Std.U8 433#usize ×
      Array Std.U64 4#usize

abbrev InnerOutput (Fields : Type) :=
  transcript.Transcript × Fields × Point × RawQM31 ×
    Option (core.result.Result (RawQM31 × Point × RawQM31)
      v6_transcript.V6TranscriptError) × Std.U32

def NoPendingSuccess
    (pending : Option (core.result.Result (RawQM31 × Point × RawQM31)
      v6_transcript.V6TranscriptError)) : Prop :=
  ∀ eta point terminal, pending ≠ some (.Ok (eta, point, terminal))

def innerBody {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (transcript0 : transcript.Transcript) (point : Point)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pending : Option (core.result.Result (RawQM31 × Point × RawQM31)
      v6_transcript.V6TranscriptError))
    (state : InnerState Fields) :
    Result (ControlFlow (InnerState Fields) (InnerOutput Fields)) :=
  v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body fieldsInst
    transcript0 point runningClaim round pending state.1 state.2.1
    state.2.2.1 state.2.2.2.1 state.2.2.2.2

private theorem inner_done_facts
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (transcript0 : transcript.Transcript) (point : Point)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pending : Option (core.result.Result (RawQM31 × Point × RawQM31)
      v6_transcript.V6TranscriptError))
    (state : InnerState Fields) (output : InnerOutput Fields)
    (edge : innerBody fieldsInst transcript0 point runningClaim round pending
      state = ok (done output))
    (canonical : CanonicalPoint point)
    (noPending : NoPendingSuccess pending) :
    NoPendingSuccess output.2.2.2.2.1 ∧
      (output.2.2.2.2.2 = 1#u32 → CanonicalPoint output.2.2.1) := by
  rcases state with ⟨iter, fields, polynomial, framed, tailLimbs⟩
  unfold innerBody at edge
  unfold v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | some sent =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨coefficient, coefficientRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨readPair, readRun, edge⟩ := edge
      rcases readPair with ⟨readResult, fieldsAfter⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨flow, branchRun, edge⟩ := edge
      cases flow with
      | Continue value =>
          repeat' first
            | rw [bind_eq_ok_iff] at edge
              obtain ⟨_, _, edge⟩ := edge
          cases edge
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              cases converted :
                  v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from
                    error <;>
                simp [converted,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                  at edge
              all_goals rw [← edge]
              all_goals constructor
              all_goals simp [NoPendingSuccess]
  | none =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨tail0, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨m0, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨tail1, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨m1, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨c0, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨tail2, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨m2, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨tail3, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨m3, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨c1, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨missing, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨polynomialBack, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨framedSlice, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨transcriptAbsorbed, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨challengePair, challengeRun, edge⟩ := edge
      rcases challengePair with ⟨challengeResult, transcriptAfter⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨challengeMapped, mapRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨flow, branchRun, edge⟩ := edge
      cases flow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at edge
              rw [← edge]
              constructor <;> simp [NoPendingSuccess]
      | Continue challenge =>
          have mappedExact := branch_eq_ok_of_continue challengeMapped
            challenge branchRun
          have challengeExact : challengeResult = .Ok challenge := by
            rw [mappedExact] at mapRun
            cases challengeResult with
            | Ok actual =>
                have actualExact : actual = challenge := by
                  simpa [core.result.Result.map_err] using mapRun
                subst actual
                rfl
            | Err error =>
                simp [core.result.Result.map_err,
                  v6_transcript.verify_compact_semantic_sumcheck.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once]
                  at mapRun
          rw [challengeExact] at challengeRun
          rw [bind_eq_ok_iff] at edge
          obtain ⟨claimAfter, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨pointAfter, pointRun, edge⟩ := edge
          have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
          rw [← outputExact]
          constructor
          · exact noPending
          · intro _
            exact canonical_point_update point pointAfter round challenge
              pointRun canonical
              (successful_challenge_qm31_canonical transcriptAbsorbed
                transcriptAfter challenge challengeRun)

private theorem inner_trace_facts
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (transcript0 : transcript.Transcript) (point : Point)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pending : Option (core.result.Result (RawQM31 × Point × RawQM31)
      v6_transcript.V6TranscriptError))
    {state : InnerState Fields} {output : InnerOutput Fields}
    (trace : ExactLoopTrace
      (innerBody fieldsInst transcript0 point runningClaim round pending)
      state output)
    (canonical : CanonicalPoint point)
    (noPending : NoPendingSuccess pending) :
    NoPendingSuccess output.2.2.2.2.1 ∧
      (output.2.2.2.2.2 = 1#u32 → CanonicalPoint output.2.2.1) := by
  induction trace with
  | done edge =>
      exact inner_done_facts fieldsInst transcript0 point
        runningClaim round pending _ _ edge canonical noPending
  | cont edge tail inductionHypothesis =>
      exact inductionHypothesis

theorem successful_semantic_inner_loop_facts
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (iter : core.ops.range.Range Std.Usize)
    (transcript0 transcriptOut : transcript.Transcript)
    (fields fieldsOut : Fields) (point pointOut : Point)
    (runningClaim claimOut : RawQM31) (round : Std.Usize)
    (polynomial : Array RawQM31 28#usize)
    (framed : Array Std.U8 433#usize)
    (tailLimbs : Array Std.U64 4#usize)
    (pending pendingOut : Option
      (core.result.Result (RawQM31 × Point × RawQM31)
        v6_transcript.V6TranscriptError))
    (canonical : CanonicalPoint point)
    (noPending : NoPendingSuccess pending)
    (run : v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0
      fieldsInst iter transcript0 fields point runningClaim round polynomial
      framed tailLimbs pending =
        ok (transcriptOut, fieldsOut, pointOut, claimOut, pendingOut, 1#u32)) :
    CanonicalPoint pointOut ∧ NoPendingSuccess pendingOut := by
  unfold v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace
    (innerBody fieldsInst transcript0 point runningClaim round pending)
    (iter, fields, polynomial, framed, tailLimbs)
    (transcriptOut, fieldsOut, pointOut, claimOut, pendingOut, 1#u32) run
  have facts := inner_trace_facts fieldsInst transcript0 point
    runningClaim round pending trace canonical noPending
  exact ⟨facts.2 rfl, facts.1⟩

abbrev OuterState (Fields : Type) :=
  core.ops.range.Range Std.Usize × transcript.Transcript × Fields × Point ×
    RawQM31 × Option (core.result.Result (RawQM31 × Point × RawQM31)
      v6_transcript.V6TranscriptError)

abbrev OuterOutput (Fields : Type) :=
  transcript.Transcript × Fields × Option
    (core.result.Result (RawQM31 × Point × RawQM31)
      v6_transcript.V6TranscriptError)

def outerBody {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields) (eta : RawQM31)
    (state : OuterState Fields) :
    Result (ControlFlow (OuterState Fields) (OuterOutput Fields)) :=
  v6_transcript.verify_compact_semantic_sumcheck_loop0.body fieldsInst eta
    state.1 state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2.1
    state.2.2.2.2.2

private theorem continuing_outer_preserves
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields) (eta : RawQM31)
    (state next : OuterState Fields)
    (edge : outerBody fieldsInst eta state = ok (cont next))
    (canonical : CanonicalPoint state.2.2.2.1)
    (noPending : NoPendingSuccess state.2.2.2.2.2) :
    CanonicalPoint next.2.2.2.1 ∧
      NoPendingSuccess next.2.2.2.2.2 := by
  rcases state with
    ⟨iter, transcript0, fields, point, runningClaim, pending⟩
  rcases next with
    ⟨iterNext, transcriptNext, fieldsNext, pointNext, claimNext, pendingNext⟩
  unfold outerBody at edge
  unfold v6_transcript.verify_compact_semantic_sumcheck_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none => cases edge
  | some round =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨framedBack, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨roundByte, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨readPair, _, edge⟩ := edge
      rcases readPair with ⟨readResult, fieldsAfterRead⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨flow, _, edge⟩ := edge
      cases flow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              cases converted :
                  v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from
                    error <;>
                simp [converted,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                  at edge
      | Continue first =>
          rw [bind_eq_ok_iff] at edge
          obtain ⟨polynomialOne, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨firstAgain, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨framedSlicePair, _, edge⟩ := edge
          rcases framedSlicePair with ⟨framedSlice, framedBack1⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨writtenSlice, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨limb0, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨twice0, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨limb1, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨twice1, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨limb2, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨twice2, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨limb3, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨twice3, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨innerOut, innerRun, edge⟩ := edge
          rcases innerOut with
            ⟨transcriptAfter, fieldsAfter, pointAfter, claimAfter,
              pendingAfter, status⟩
          have innerFacts : NoPendingSuccess pendingAfter ∧
              (status = 1#u32 → CanonicalPoint pointAfter) := by
            unfold v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0
              at innerRun
            obtain ⟨innerTrace⟩ := loop_success_yields_exact_trace
              (innerBody fieldsInst transcript0 point runningClaim round pending)
              ({ start := 1#usize,
                 «end» := v6_onefold.V6_SEMANTIC_SENT_VALUES },
                fieldsAfterRead, polynomialOne, framedBack1 writtenSlice,
                Array.make 4#usize [twice0, twice1, twice2, twice3])
              (transcriptAfter, fieldsAfter, pointAfter, claimAfter,
                pendingAfter, status) innerRun
            exact inner_trace_facts fieldsInst transcript0 point runningClaim
              round pending innerTrace canonical noPending
          split at edge <;> rename_i statusOne
          ·
            have exact := ControlFlow.cont.inj (Result.ok.inj edge)
            simp only [Prod.mk.injEq] at exact
            rcases exact with
              ⟨iterExact, transcriptExact, fieldsExact, pointExact,
                claimExact, pendingExact⟩
            subst pointNext
            subst pendingNext
            exact ⟨innerFacts.2 statusOne, innerFacts.1⟩
          · cases pendingAfter <;> simp at edge

private theorem done_outer_success_canonical
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields) (eta : RawQM31)
    (state : OuterState Fields) (output : OuterOutput Fields)
    (edge : outerBody fieldsInst eta state = ok (done output))
    (canonical : CanonicalPoint state.2.2.2.1)
    (noPending : NoPendingSuccess state.2.2.2.2.2)
    (etaOut : RawQM31) (pointOut : Point) (claimOut : RawQM31)
    (success : output.2.2 = some (.Ok (etaOut, pointOut, claimOut))) :
    CanonicalPoint pointOut := by
  rcases state with
    ⟨iter, transcript0, fields, point, runningClaim, pending⟩
  unfold outerBody at edge
  unfold v6_transcript.verify_compact_semantic_sumcheck_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
      rw [← outputExact] at success
      simp only [Option.some.injEq, core.result.Result.Ok.injEq,
        Prod.mk.injEq] at success
      rw [← success.2.1]
      exact canonical
  | some round =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨framedBack, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨roundByte, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨readPair, _, edge⟩ := edge
      rcases readPair with ⟨readResult, fieldsAfterRead⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨flow, _, edge⟩ := edge
      cases flow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              cases converted :
                  v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from
                    error <;>
                simp [converted,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                  at edge
              all_goals subst output
              all_goals simp at success
      | Continue first =>
          rw [bind_eq_ok_iff] at edge
          obtain ⟨polynomialOne, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨firstAgain, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨framedSlicePair, _, edge⟩ := edge
          rcases framedSlicePair with ⟨framedSlice, framedBack1⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨writtenSlice, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨limb0, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨twice0, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨limb1, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨twice1, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨limb2, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨twice2, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨limb3, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨twice3, _, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨innerOut, innerRun, edge⟩ := edge
          rcases innerOut with
            ⟨transcriptAfter, fieldsAfter, pointAfter, claimAfter,
              pendingAfter, status⟩
          have innerFacts : NoPendingSuccess pendingAfter ∧
              (status = 1#u32 → CanonicalPoint pointAfter) := by
            unfold v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0
              at innerRun
            obtain ⟨innerTrace⟩ := loop_success_yields_exact_trace
              (innerBody fieldsInst transcript0 point runningClaim round pending)
              ({ start := 1#usize,
                 «end» := v6_onefold.V6_SEMANTIC_SENT_VALUES },
                fieldsAfterRead, polynomialOne, framedBack1 writtenSlice,
                Array.make 4#usize [twice0, twice1, twice2, twice3])
              (transcriptAfter, fieldsAfter, pointAfter, claimAfter,
                pendingAfter, status) innerRun
            exact inner_trace_facts fieldsInst transcript0 point runningClaim
              round pending innerTrace canonical noPending
          split at edge
          · cases edge
          ·
            cases pendingAfter with
            | none =>
                simp only at edge
                have outputExact :=
                  ControlFlow.done.inj (Result.ok.inj edge)
                rw [← outputExact] at success
                simp at success
            | some pendingResult =>
                have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
                rw [← outputExact] at success
                cases pendingResult with
                | Err error => simp at success
                | Ok values =>
                    rcases values with ⟨etaValue, pointValue, terminalValue⟩
                    exact False.elim
                      (innerFacts.1 etaValue pointValue terminalValue rfl)

private theorem outer_trace_success_canonical
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields) (eta : RawQM31)
    {state : OuterState Fields} {output : OuterOutput Fields}
    (trace : ExactLoopTrace (outerBody fieldsInst eta) state output)
    (canonical : CanonicalPoint state.2.2.2.1)
    (noPending : NoPendingSuccess state.2.2.2.2.2)
    (etaOut : RawQM31) (pointOut : Point) (claimOut : RawQM31)
    (success : output.2.2 = some (.Ok (etaOut, pointOut, claimOut))) :
    CanonicalPoint pointOut := by
  induction trace with
  | done edge =>
      exact done_outer_success_canonical fieldsInst eta _ _ edge canonical
        noPending etaOut pointOut claimOut success
  | @cont _ next _ edge tail inductionHypothesis =>
      have nextFacts := continuing_outer_preserves fieldsInst eta _ next edge
        canonical noPending
      exact inductionHypothesis nextFacts.1 nextFacts.2 success

private theorem zero_canonical :
    GeneratedCanonicalQM31 field.QM31.ZERO := by
  norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus, field.QM31.ZERO,
    field.CM31.ZERO, field.M31.ZERO, field.P]

private theorem repeated_zero_point_canonical :
    CanonicalPoint (Array.repeat 10#usize field.QM31.ZERO) := by
  unfold CanonicalPoint
  intro index bound
  let length : Std.Usize := 10#usize
  change GeneratedCanonicalQM31
    (Array.repeat length field.QM31.ZERO).val[index]!
  have exact : (Array.repeat length field.QM31.ZERO).val[index]! =
      field.QM31.ZERO := by
    exact List.getElem!_replicate field.QM31.ZERO (by
      simpa [length] using bound)
  rw [exact]
  exact zero_canonical

theorem successful_verify_compact_semantic_sumcheck_point_canonical
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (transcriptIn transcriptOut : transcript.Transcript)
    (fields fieldsOut : Fields) (eta : RawQM31) (point : Point)
    (terminal : RawQM31)
    (run : v6_transcript.verify_compact_semantic_sumcheck fieldsInst
      transcriptIn fields =
        ok (.Ok (eta, point, terminal), transcriptOut, fieldsOut)) :
    CanonicalPoint point := by
  unfold v6_transcript.verify_compact_semantic_sumcheck at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨readPair, _, run⟩ := run
  rcases readPair with ⟨readResult, fieldsAfterRead⟩
  rw [bind_eq_ok_iff] at run
  obtain ⟨readFlow, _, run⟩ := run
  cases readFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          cases converted :
              v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from
                error <;>
            simp [converted,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
              at run
  | Continue maskedClaim =>
      rw [bind_eq_ok_iff] at run
      obtain ⟨beginPair, _, run⟩ := run
      rcases beginPair with ⟨beginResult, transcriptAfterBegin⟩
      rw [bind_eq_ok_iff] at run
      obtain ⟨beginMapped, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨beginFlow, _, run⟩ := run
      cases beginFlow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at run
      | Continue runningClaim =>
          rw [bind_eq_ok_iff] at run
          obtain ⟨loopOut, loopRun, run⟩ := run
          rcases loopOut with
            ⟨transcriptAfter, fieldsAfter, pendingAfter⟩
          cases pendingAfter with
          | none => simp at run
          | some pendingResult =>
              have outputExact :
                  pendingResult = .Ok (eta, point, terminal) ∧
                    transcriptAfter = transcriptOut ∧
                    fieldsAfter = fieldsOut := by
                simpa using run
              have pendingExact := outputExact.1
              subst pendingResult
              unfold v6_transcript.verify_compact_semantic_sumcheck_loop0
                at loopRun
              obtain ⟨trace⟩ := loop_success_yields_exact_trace
                (outerBody fieldsInst runningClaim)
                ({ start := 0#usize,
                   «end» := v6_onefold.V6_SEMANTIC_ROUNDS },
                  transcriptAfterBegin, fieldsAfterRead,
                  Array.repeat 10#usize field.QM31.ZERO, maskedClaim, none)
                (transcriptAfter, fieldsAfter,
                  some (.Ok (eta, point, terminal))) loopRun
              exact outer_trace_success_canonical fieldsInst runningClaim trace
                repeated_zero_point_canonical
                (by simp [NoPendingSuccess]) eta point terminal rfl

#print axioms successful_semantic_inner_loop_facts
#print axioms successful_verify_compact_semantic_sumcheck_point_canonical

end V7CallerCurrentReleaseR30SemanticPointCanonical
