import V7CallerCurrentReleaseR30FixedFieldCanonical
import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Canonicality of the decoded final-256 vector

The generated decoder appends one successful fixed-field read per loop step.
This proof follows the exact loop trace and carries canonical membership of
the decoded vector without evaluating any concrete 256-element term.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30Final256Canonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace

abbrev RawQM31 := field.QM31
abbrev Decoded := alloc.vec.Vec RawQM31
abbrev Encoded := alloc.vec.Vec Std.U8
abbrev LoopState (Fields : Type) :=
  core.ops.range.Range Std.Usize × Fields × Decoded × Encoded
abbrev LoopOutput (Fields : Type) := Fields × Decoded × Encoded ×
  Option (core.result.Result (Array RawQM31 256#usize)
    v6_transcript.V6TranscriptError)

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def CanonicalVec (values : Decoded) : Prop :=
  ∀ value, value ∈ values.val → GeneratedCanonicalQM31 value

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

private theorem push_exact
    (values valuesOut : Decoded) (value : RawQM31)
    (run : alloc.vec.Vec.push values value = ok valuesOut) :
    valuesOut.val = values.val ++ [value] := by
  unfold alloc.vec.Vec.push at run
  simp only at run
  split at run
  · simpa [List.concat_eq_append] using
      congrArg Subtype.val (Result.ok.inj run).symm
  · cases run

def loopBody {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (state : LoopState Fields) :
    Result (ControlFlow (LoopState Fields) (LoopOutput Fields)) :=
  v6_transcript.decode_and_absorb_final256_loop.body fieldsInst
    state.1 state.2.1 state.2.2.1 state.2.2.2

private theorem continuing_body_preserves_canonical
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (state next : LoopState Fields)
    (edge : loopBody fieldsInst state = ok (cont next))
    (canonical : CanonicalVec state.2.2.1) :
    CanonicalVec next.2.2.1 := by
  rcases state with ⟨iter, fields, decoded, encoded⟩
  rcases next with ⟨iterOut, fieldsOut, decodedOut, encodedOut⟩
  change CanonicalVec decoded at canonical
  change CanonicalVec decodedOut
  unfold loopBody at edge
  unfold v6_transcript.decode_and_absorb_final256_loop.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none => cases edge
  | some ordinal =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨readPair, readRun, edge⟩ := edge
      rcases readPair with ⟨readResult, fieldsAfter⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨flow, branchRun, edge⟩ := edge
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
      | Continue value =>
          have readExact := branch_eq_ok_of_continue readResult value branchRun
          have valueCanonical := readCanonical fields value fieldsAfter (by
            rw [readExact] at readRun
            exact readRun)
          simp only at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨decodedAfter, pushRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨offset, offsetRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨slicePair, sliceRun, edge⟩ := edge
          rcases slicePair with ⟨slice, sliceBack⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨prefixPair, prefixRun, edge⟩ := edge
          rcases prefixPair with ⟨prefixSlice, prefixBack⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨written, writeRun, edge⟩ := edge
          simp only [Result.ok.injEq, ControlFlow.cont.injEq,
            Prod.mk.injEq] at edge
          have decodedExact : decodedOut = decodedAfter := edge.2.2.1.symm
          rw [decodedExact]
          unfold CanonicalVec
          rw [push_exact decoded decodedAfter value pushRun]
          intro candidate membership
          simp only [List.mem_append, List.mem_singleton] at membership
          rcases membership with old | current
          · exact canonical candidate old
          · subst candidate
            exact valueCanonical

private theorem done_body_facts
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (state : LoopState Fields) (output : LoopOutput Fields)
    (edge : loopBody fieldsInst state = ok (done output))
    (canonical : CanonicalVec state.2.2.1) :
    CanonicalVec output.2.1 ∧
      ∀ values : Array RawQM31 256#usize,
        output.2.2.2 ≠ some (.Ok values) := by
  rcases state with ⟨iter, fields, decoded, encoded⟩
  change CanonicalVec decoded at canonical
  unfold loopBody at edge
  unfold v6_transcript.decode_and_absorb_final256_loop.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
      rw [← outputExact]
      exact ⟨canonical, by intro values; simp⟩
  | some ordinal =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨readPair, readRun, edge⟩ := edge
      rcases readPair with ⟨readResult, fieldsAfter⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨flow, branchRun, edge⟩ := edge
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
              all_goals rw [← edge]
              all_goals exact ⟨canonical, by intro values; simp⟩
      | Continue value =>
          simp only at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨decodedAfter, pushRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨offset, offsetRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨slicePair, sliceRun, edge⟩ := edge
          rcases slicePair with ⟨slice, sliceBack⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨prefixPair, prefixRun, edge⟩ := edge
          rcases prefixPair with ⟨prefixSlice, prefixBack⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨written, writeRun, edge⟩ := edge
          cases edge

private theorem trace_facts
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    {state : LoopState Fields} {output : LoopOutput Fields}
    (trace : ExactLoopTrace (loopBody fieldsInst) state output)
    (canonical : CanonicalVec state.2.2.1) :
    CanonicalVec output.2.1 ∧
      ∀ values : Array RawQM31 256#usize,
        output.2.2.2 ≠ some (.Ok values) := by
  induction trace with
  | done edge => exact done_body_facts fieldsInst _ _ edge canonical
  | @cont _ next _ edge tail inductionHypothesis =>
      exact inductionHypothesis
        (continuing_body_preserves_canonical fieldsInst readCanonical _ next
          edge canonical)

theorem successful_final256_loop_facts
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (iter : core.ops.range.Range Std.Usize)
    (fields fieldsOut : Fields) (decoded decodedOut : Decoded)
    (encoded encodedOut : Encoded)
    (pending : Option (core.result.Result (Array RawQM31 256#usize)
      v6_transcript.V6TranscriptError))
    (canonical : CanonicalVec decoded)
    (run : v6_transcript.decode_and_absorb_final256_loop fieldsInst iter fields
      decoded encoded = ok (fieldsOut, decodedOut, encodedOut, pending)) :
    CanonicalVec decodedOut ∧
      ∀ values : Array RawQM31 256#usize, pending ≠ some (.Ok values) := by
  unfold v6_transcript.decode_and_absorb_final256_loop at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace (loopBody fieldsInst)
    (iter, fields, decoded, encoded)
    (fieldsOut, decodedOut, encodedOut, pending) run
  exact trace_facts fieldsInst readCanonical trace canonical

def CanonicalFinal256 (values : Array RawQM31 256#usize) : Prop :=
  ∀ index, index < values.val.length →
    GeneratedCanonicalQM31 values.val[index]!

theorem successful_decode_and_absorb_final256_canonical
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (transcriptIn transcriptOut : transcript.Transcript)
    (fields fieldsOut : Fields) (values : Array RawQM31 256#usize)
    (run : v6_transcript.decode_and_absorb_final256 fieldsInst transcriptIn
      fields = ok (core.result.Result.Ok values, transcriptOut, fieldsOut)) :
    CanonicalFinal256 values := by
  unfold v6_transcript.decode_and_absorb_final256 at run
  simp only at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨encodedLength, encodedLengthRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨encoded, encodedRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨loopOut, loopRun, run⟩ := run
  rcases loopOut with ⟨fieldsAfter, decodedAfter, encodedAfter, pending⟩
  have initialCanonical : CanonicalVec
      (alloc.vec.Vec.with_capacity RawQM31
        v6_onefold.V6_FINAL_QM31_VALUES) := by
    intro value membership
    simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] at membership
  have loopFacts := successful_final256_loop_facts fieldsInst readCanonical
    { start := 0#usize, «end» := v6_onefold.V6_FINAL_QM31_VALUES }
    fields fieldsAfter
    (alloc.vec.Vec.with_capacity RawQM31
      v6_onefold.V6_FINAL_QM31_VALUES)
    decodedAfter encoded encodedAfter pending initialCanonical loopRun
  cases pending with
  | some pendingResult =>
      have outputExact := Result.ok.inj run
      have pendingSuccess :
          some pendingResult = some (.Ok values) := by
        exact congrArg (fun result => some result)
          (congrArg Prod.fst outputExact)
      exact False.elim (loopFacts.2 values pendingSuccess)
  | none =>
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨transcriptAfter, absorbRun, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨boxed, boxedRun, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨converted, convertedRun, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨arrayOut, expectRun, run⟩ := run
      have outputExact := Result.ok.inj run
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at outputExact
      have valuesExact : arrayOut = values := outputExact.1
      have boxedExact : boxed.val = decodedAfter.val := by
        simpa [alloc.vec.Vec.into_boxed_slice] using
          (congrArg Subtype.val (Result.ok.inj boxedRun)).symm
      have convertedExact : converted = .Ok arrayOut := by
        cases converted <;>
          simp [core.result.Result.expect] at expectRun
        simpa [core.result.Result.expect] using expectRun
      unfold BoxArray.Insts.CoreConvertTryFromBoxSliceBoxSlice.try_from at convertedRun
      split at convertedRun
      · have arrayListExact : arrayOut.val = boxed.val := by
          rw [convertedExact] at convertedRun
          exact congrArg Subtype.val
            (core.result.Result.Ok.inj (Result.ok.inj convertedRun)).symm
        rw [← valuesExact]
        unfold CanonicalFinal256
        rw [arrayListExact, boxedExact]
        intro index indexBound
        have valueExact : decodedAfter.val[index] =
            decodedAfter.val[index]! := by
          symm
          apply List.getElem!_of_getElem?
          simp
        rw [← valueExact]
        exact loopFacts.1 _ (List.getElem_mem indexBound)
      · rw [convertedExact] at convertedRun
        cases Result.ok.inj convertedRun

#print axioms successful_final256_loop_facts
#print axioms successful_decode_and_absorb_final256_canonical

end V7CallerCurrentReleaseR30Final256Canonical
