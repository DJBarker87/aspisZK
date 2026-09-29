import V7CallerCurrentReleaseR30RelationFieldInnerCanonical
import V7CallerCurrentReleaseR26RelationDecodeSemantics

/-!
# Canonicality through the complete compact relation-field decoder

This module lifts the one-row symbolic decoder proof through the generated
four-row mutable-slice loop.  It never evaluates a concrete decoder trace.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30RelationFieldsCanonical

attribute [-simp] List.getElem!_eq_getElem?_getD

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR30RelationFieldInnerCanonical

abbrev RawQM31 := field.QM31
abbrev Row := Array RawQM31 6#usize
abbrev OuterIter := core.slice.iter.IterMut Row
private abbrev fourUsize : Std.Usize := 4#usize
private abbrev sixUsize : Std.Usize := 6#usize

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩
local instance : Inhabited Row := ⟨Array.repeat 6#usize field.QM31.ZERO⟩

def RowCanonical (row : Row) : Prop :=
  ∀ index, index < row.val.length →
    GeneratedCanonicalQM31 row.val[index]!

def CanonicalRows (rows : Slice Row) : Prop :=
  ∀ index, index < rows.length → RowCanonical rows.val[index]!

def OuterBackPreservesCanonical (length : Nat)
    (back : OuterIter → OuterIter) : Prop :=
  ∀ iter, iter.slice.length = length → CanonicalRows iter.slice →
    CanonicalRows (back iter).slice ∧ (back iter).slice.length = length

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem canonical_rows_set
    (rows : Slice Row) (index : Nat) (row : Row)
    (active : index < rows.length)
    (canonical : CanonicalRows rows) (rowCanonical : RowCanonical row) :
    CanonicalRows (rows.setAtNat index row) := by
  intro target targetBound
  have oldTargetBound : target < rows.length := by
    simpa [Slice.setAtNat] using targetBound
  by_cases same : target = index
  · subst target
    simpa [Slice.setAtNat, List.getElem!_eq_getElem?_getD, active]
      using rowCanonical
  · have oldCanonical := canonical target oldTargetBound
    simpa [Slice.setAtNat, active, List.getElem!_eq_getElem?_getD, same]
      using oldCanonical

private theorem outer_iterator_some_exact
    (iter iterNext : OuterIter)
    (nextBack : OuterIter → Option Row → OuterIter) (row : Row)
    (run : core.slice.iter.IteratorIterMut.next iter =
      ok (some row, iterNext, nextBack)) :
    iter.i < iter.slice.length ∧ iterNext.slice = iter.slice := by
  unfold core.slice.iter.IteratorIterMut.next at run
  split at run
  · rename_i active
    simp only [Result.ok.injEq, Prod.mk.injEq,
      Option.some.injEq] at run
    rw [← run.2.1]
    exact ⟨active, rfl⟩
  · simp at run

private theorem outer_iterator_some_back_preserves
    (iter iterNext : OuterIter)
    (nextBack : OuterIter → Option Row → OuterIter)
    (oldRow row : Row)
    (run : core.slice.iter.IteratorIterMut.next iter =
      ok (some oldRow, iterNext, nextBack))
    (rowCanonical : RowCanonical row)
    (length : Nat) (iterLength : iter.slice.length = length) :
    ∀ candidate, candidate.slice.length = length →
      CanonicalRows candidate.slice →
      CanonicalRows (nextBack candidate (some row)).slice ∧
        (nextBack candidate (some row)).slice.length = length := by
  unfold core.slice.iter.IteratorIterMut.next at run
  split at run
  · rename_i active
    simp only [Result.ok.injEq, Prod.mk.injEq,
      Option.some.injEq] at run
    have backExact := run.2.2
    rw [← backExact]
    intro candidate candidateLength candidateCanonical
    have activeCandidate : iter.i < candidate.slice.length := by
      simpa [candidateLength, iterLength] using active
    constructor
    · exact canonical_rows_set candidate.slice iter.i row activeCandidate
        candidateCanonical rowCanonical
    · simpa [Slice.setAtNat] using candidateLength
  · simp at run

private theorem outer_iterator_none_back_preserves
    (iter iterNext : OuterIter)
    (nextBack : OuterIter → Option Row → OuterIter)
    (run : core.slice.iter.IteratorIterMut.next iter =
      ok (none, iterNext, nextBack))
    (canonical : CanonicalRows iter.slice) (length : Nat)
    (iterLength : iter.slice.length = length) :
    CanonicalRows (nextBack iterNext none).slice ∧
      (nextBack iterNext none).slice.length = length := by
  unfold core.slice.iter.IteratorIterMut.next at run
  split at run
  · simp at run
  · simp only [Result.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨_, iterExact, backExact⟩
    rw [← iterExact, ← backExact]
    exact ⟨canonical, iterLength⟩

abbrev OuterState (Fields : Type) :=
  OuterIter × (OuterIter → OuterIter) × Fields

abbrev OuterOutput (Fields : Type) :=
  Fields × (Option (core.result.Result
    (Array Row 4#usize) v6_transcript.V6TranscriptError)) × OuterIter

structure OuterStep {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (state next : OuterState Fields) : Type where
  oldRow : Row
  nextBack : OuterIter → Option Row → OuterIter
  innerIter : core.slice.iter.IterMut RawQM31
  innerBack : core.slice.iter.IterMut RawQM31 → Row
  innerOut : core.slice.iter.IterMut RawQM31
  iteratorSuccess :
    core.slice.iter.IteratorIterMut.next state.1 =
      ok (some oldRow, next.1, nextBack)
  intoSuccess :
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
      oldRow = ok (innerIter, innerBack)
  innerSuccess :
    v6_transcript.decode_compact_relation_fields_loop0_loop0 fieldsInst
      innerIter (fun iter => iter) state.2.2 =
        ok (next.2.2, none, innerOut)
  backExact :
    next.2.1 = fun iter =>
      state.2.1 (nextBack iter (some (innerBack innerOut)))

private theorem continuing_outer_body_exposes_step
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (state next : OuterState Fields)
    (edge :
      v6_transcript.decode_compact_relation_fields_loop0.body fieldsInst
          state.1 state.2.1 state.2.2 = ok (cont next)) :
    Nonempty (OuterStep fieldsInst state next) := by
  rcases state with ⟨iter, back, fields⟩
  rcases next with ⟨iterNext, backNext, fieldsNext⟩
  unfold v6_transcript.decode_compact_relation_fields_loop0.body at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorTriple, iteratorRun, edge⟩ := edge
  rcases iteratorTriple with ⟨option, iterAfter, nextBack⟩
  cases option with
  | none => cases edge
  | some oldRow =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨intoPair, intoRun, edge⟩ := edge
      rcases intoPair with ⟨innerIter, innerBack⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨innerTriple, innerRun, edge⟩ := edge
      rcases innerTriple with ⟨fieldsAfter, pending, innerOut⟩
      cases pending with
      | some pendingResult => cases edge
      | none =>
          simp only [Result.ok.injEq, ControlFlow.cont.injEq,
            Prod.mk.injEq] at edge
          rcases edge with ⟨iterExact, backExact, fieldsExact⟩
          subst iterAfter
          subst fieldsAfter
          exact ⟨{
            oldRow := oldRow
            nextBack := nextBack
            innerIter := innerIter
            innerBack := innerBack
            innerOut := innerOut
            iteratorSuccess := iteratorRun
            intoSuccess := intoRun
            innerSuccess := innerRun
            backExact := backExact.symm }⟩

private theorem done_outer_none_exposes_iterator
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (state : OuterState Fields) (output : OuterOutput Fields)
    (pendingNone : output.2.1 = none)
    (edge :
      v6_transcript.decode_compact_relation_fields_loop0.body fieldsInst
          state.1 state.2.1 state.2.2 = ok (done output)) :
    ∃ iterAfter nextBack,
      core.slice.iter.IteratorIterMut.next state.1 =
        ok (none, iterAfter, nextBack) ∧
      output = (state.2.2, none, state.2.1 (nextBack iterAfter none)) := by
  rcases state with ⟨iter, back, fields⟩
  unfold v6_transcript.decode_compact_relation_fields_loop0.body at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorTriple, iteratorRun, edge⟩ := edge
  rcases iteratorTriple with ⟨option, iterAfter, nextBack⟩
  cases option with
  | none =>
      refine ⟨iterAfter, nextBack, iteratorRun, ?_⟩
      exact (ControlFlow.done.inj (Result.ok.inj edge)).symm
  | some oldRow =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨intoPair, intoRun, edge⟩ := edge
      rcases intoPair with ⟨innerIter, innerBack⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨innerTriple, innerRun, edge⟩ := edge
      rcases innerTriple with ⟨fieldsAfter, pending, innerOut⟩
      cases pending with
      | none => cases edge
      | some pendingResult =>
          simp only [Result.ok.injEq, ControlFlow.done.injEq] at edge
          rw [← edge] at pendingNone
          simp at pendingNone

private theorem done_outer_pending_classification
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (state : OuterState Fields) (output : OuterOutput Fields)
    (edge :
      v6_transcript.decode_compact_relation_fields_loop0.body fieldsInst
          state.1 state.2.1 state.2.2 = ok (done output)) :
    output.2.1 = none ∨
      ∃ error : v6_transcript.V6TranscriptError,
        output.2.1 = some (.Err error) := by
  rcases state with ⟨iter, back, fields⟩
  unfold v6_transcript.decode_compact_relation_fields_loop0.body at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorTriple, iteratorRun, edge⟩ := edge
  rcases iteratorTriple with ⟨option, iterAfter, nextBack⟩
  cases option with
  | none =>
      have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
      rw [← outputExact]
      exact Or.inl rfl
  | some oldRow =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨intoPair, intoRun, edge⟩ := edge
      rcases intoPair with ⟨innerIter, innerBack⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨innerTriple, innerRun, edge⟩ := edge
      rcases innerTriple with ⟨fieldsAfter, pending, innerOut⟩
      cases pending with
      | none => cases edge
      | some pendingResult =>
          cases pendingResult with
          | Ok values =>
              exact False.elim
                (successful_inner_relation_field_loop_never_pending_success
                  fieldsInst innerIter (fun iter => iter) fields fieldsAfter
                  (some (.Ok values)) innerOut innerRun values rfl)
          | Err error =>
              have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
              rw [← outputExact]
              exact Or.inr ⟨error, rfl⟩

private theorem exact_outer_trace_never_returns_pending_success
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    {state : OuterState Fields} {output : OuterOutput Fields}
    (trace : ExactLoopTrace
      (fun state : OuterState Fields =>
        v6_transcript.decode_compact_relation_fields_loop0.body
          fieldsInst state.1 state.2.1 state.2.2)
      state output) :
    ∀ values : Array Row 4#usize, output.2.1 ≠ some (.Ok values) := by
  induction trace with
  | done edge =>
      rcases done_outer_pending_classification fieldsInst _ _ edge with
        pendingNone | ⟨error, pendingError⟩
      · intro values pendingSuccess
        rw [pendingNone] at pendingSuccess
        simp at pendingSuccess
      · intro values pendingSuccess
        rw [pendingError] at pendingSuccess
        simp at pendingSuccess
  | cont edge tail inductionHypothesis => exact inductionHypothesis

theorem successful_outer_relation_field_loop_never_pending_success
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (iter : OuterIter) (back : OuterIter → OuterIter)
    (fields fieldsOut : Fields)
    (pending : Option (core.result.Result
      (Array Row 4#usize) v6_transcript.V6TranscriptError))
    (backOut : OuterIter)
    (run :
      v6_transcript.decode_compact_relation_fields_loop0 fieldsInst
        iter back fields = ok (fieldsOut, pending, backOut)) :
    ∀ values, pending ≠ some (.Ok values) := by
  unfold v6_transcript.decode_compact_relation_fields_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace
    (fun state : OuterState Fields =>
      v6_transcript.decode_compact_relation_fields_loop0.body
        fieldsInst state.1 state.2.1 state.2.2)
    (iter, back, fields) (fieldsOut, pending, backOut) run
  exact exact_outer_trace_never_returns_pending_success fieldsInst trace

private theorem inner_back_row_canonical
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (oldRow : Row)
    (innerIter : core.slice.iter.IterMut RawQM31)
    (innerBack : core.slice.iter.IterMut RawQM31 → Row)
    (fields fieldsOut : Fields)
    (innerOut : core.slice.iter.IterMut RawQM31)
    (oldCanonical : RowCanonical oldRow)
    (intoRun :
      MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
        oldRow = ok (innerIter, innerBack))
    (innerRun :
      v6_transcript.decode_compact_relation_fields_loop0_loop0 fieldsInst
        innerIter (fun iter => iter) fields = ok (fieldsOut, none, innerOut)) :
    RowCanonical (innerBack innerOut) := by
  unfold
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
    at intoRun
  simp only [Result.ok.injEq, Prod.mk.injEq] at intoRun
  rcases intoRun with ⟨rfl, rfl⟩
  have initialCanonical : CanonicalSlice (Array.to_slice oldRow) := by
    simpa [CanonicalSlice, RowCanonical, Array.to_slice] using oldCanonical
  have decodedCanonical := successful_inner_relation_field_loop_canonical
    fieldsInst readCanonical
    ({ slice := Array.to_slice oldRow } : core.slice.iter.IterMut RawQM31)
    (fun iter => iter) fields fieldsOut innerOut 6 initialCanonical
    oldRow.property
    (by
      intro iter iterLength iterCanonical
      exact ⟨iterCanonical, iterLength⟩)
    innerRun
  by_cases correctLength : innerOut.slice.val.length = 6
  · intro index indexBound
    have decodedBound : index < innerOut.slice.length := by
      simpa [Array.from_slice, correctLength] using indexBound
    simpa [Array.from_slice, correctLength]
      using decodedCanonical index decodedBound
  · simpa [Array.from_slice, correctLength] using oldCanonical

private theorem exact_outer_trace_returns_canonical
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value) :
    ∀ (length : Nat) {state output},
      ExactLoopTrace
        (fun state : OuterState Fields =>
          v6_transcript.decode_compact_relation_fields_loop0.body
            fieldsInst state.1 state.2.1 state.2.2)
        state output →
      CanonicalRows state.1.slice →
      state.1.slice.length = length →
      OuterBackPreservesCanonical length state.2.1 →
      output.2.1 = none →
      CanonicalRows output.2.2.slice := by
  intro length state output trace iterCanonical iterLength backPreserves
    pendingNone
  cases trace with
  | done edge =>
      obtain ⟨iterAfter, nextBack, iteratorRun, outputExact⟩ :=
        done_outer_none_exposes_iterator fieldsInst state output pendingNone edge
      rw [outputExact]
      obtain ⟨nextCanonical, nextLength⟩ :=
        outer_iterator_none_back_preserves state.1 iterAfter nextBack
          iteratorRun iterCanonical length iterLength
      exact (backPreserves _ nextLength nextCanonical).1
  | @cont _ next _ edge tail =>
      obtain ⟨step⟩ := continuing_outer_body_exposes_step
        fieldsInst state next edge
      have iteratorExact := outer_iterator_some_exact state.1 next.1
        step.nextBack step.oldRow step.iteratorSuccess
      have oldRowCanonical : RowCanonical step.oldRow := by
        have := iterCanonical state.1.i iteratorExact.1
        have iteratorRun := step.iteratorSuccess
        unfold core.slice.iter.IteratorIterMut.next at iteratorRun
        split at iteratorRun
        · simp only [Result.ok.injEq, Prod.mk.injEq,
            Option.some.injEq] at iteratorRun
          have sliceExact :
              state.1.slice[state.1.i]'iteratorExact.1 =
                state.1.slice.val[state.1.i]! := by
            calc
              state.1.slice[state.1.i] = state.1.slice[state.1.i]! :=
                Slice.Inhabited_getElem_eq_getElem! state.1.slice state.1.i
                  iteratorExact.1
              _ = state.1.slice.val[state.1.i]! :=
                Slice.getElem!_Nat_eq state.1.slice state.1.i
          have oldRowExact :
              step.oldRow = state.1.slice.val[state.1.i]! :=
            iteratorRun.1.symm.trans sliceExact
          rw [oldRowExact]
          exact this
        · simp at iteratorRun
      have newRowCanonical := inner_back_row_canonical fieldsInst readCanonical
        step.oldRow step.innerIter step.innerBack state.2.2 next.2.2
        step.innerOut oldRowCanonical step.intoSuccess step.innerSuccess
      have nextIterCanonical : CanonicalRows next.1.slice := by
        rw [iteratorExact.2]
        exact iterCanonical
      have nextIterLength : next.1.slice.length = length := by
        rw [iteratorExact.2]
        exact iterLength
      have nextBackPreserves :
          OuterBackPreservesCanonical length next.2.1 := by
        rw [step.backExact]
        intro candidate candidateLength candidateCanonical
        obtain ⟨updatedCanonical, updatedLength⟩ :=
          outer_iterator_some_back_preserves state.1 next.1 step.nextBack
            step.oldRow (step.innerBack step.innerOut) step.iteratorSuccess
            newRowCanonical length iterLength candidate candidateLength
            candidateCanonical
        exact backPreserves _ updatedLength updatedCanonical
      exact exact_outer_trace_returns_canonical fieldsInst readCanonical length
        tail nextIterCanonical nextIterLength nextBackPreserves pendingNone

theorem successful_outer_relation_field_loop_canonical
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (iter : OuterIter) (back : OuterIter → OuterIter)
    (fields fieldsOut : Fields) (backOut : OuterIter) (length : Nat)
    (iterCanonical : CanonicalRows iter.slice)
    (iterLength : iter.slice.length = length)
    (backPreserves : OuterBackPreservesCanonical length back)
    (run :
      v6_transcript.decode_compact_relation_fields_loop0 fieldsInst
        iter back fields = ok (fieldsOut, none, backOut)) :
    CanonicalRows backOut.slice := by
  unfold v6_transcript.decode_compact_relation_fields_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace
    (fun state : OuterState Fields =>
      v6_transcript.decode_compact_relation_fields_loop0.body
        fieldsInst state.1 state.2.1 state.2.2)
    (iter, back, fields) (fieldsOut, none, backOut) run
  exact exact_outer_trace_returns_canonical fieldsInst readCanonical length trace
    iterCanonical iterLength backPreserves rfl

def DecodedCanonical (decoded : Array Row 4#usize) : Prop :=
  ∀ rowIndex, rowIndex < decoded.val.length →
    RowCanonical decoded.val[rowIndex]!

private theorem zero_canonical :
    GeneratedCanonicalQM31 field.QM31.ZERO := by
  norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus, field.QM31.ZERO,
    field.CM31.ZERO, field.M31.ZERO, field.P]

private theorem array_repeat_getElemBang
    {T : Type} [Inhabited T] (length : Std.Usize) (value : T)
    (index : Nat) (bound : index < length.val) :
    (Array.repeat length value).val[index]! = value := by
  exact List.getElem!_replicate value bound

private theorem repeated_zero_rows_canonical :
    CanonicalRows (Array.to_slice
      (Array.repeat 4#usize (Array.repeat 6#usize field.QM31.ZERO))) := by
  intro rowIndex rowBound coefficient coefficientBound
  have rowBound' : rowIndex < 4 := by
    simpa [Array.to_slice, Array.repeat] using rowBound
  change GeneratedCanonicalQM31
    (getElem! (getElem! (Array.repeat fourUsize
      (Array.repeat sixUsize field.QM31.ZERO)).val rowIndex).val
        coefficient)
  have rowExact := array_repeat_getElemBang fourUsize
    (Array.repeat sixUsize field.QM31.ZERO) rowIndex (by
      simpa [fourUsize] using rowBound')
  rw [rowExact]
  have coefficientBound' : coefficient < 6 := by
    simpa [Array.repeat] using coefficientBound
  have coefficientExact := array_repeat_getElemBang sixUsize
    field.QM31.ZERO coefficient (by
      simpa [sixUsize] using coefficientBound')
  rw [coefficientExact]
  exact zero_canonical

theorem successful_relation_field_decode_canonical
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (fields fieldsOut : Fields) (decoded : Array Row 4#usize)
    (run :
      v6_transcript.decode_compact_relation_fields fieldsInst fields =
        ok (.Ok decoded, fieldsOut)) :
    DecodedCanonical decoded := by
  unfold v6_transcript.decode_compact_relation_fields at run
  simp only [Aeneas.Std.lift, bind_tc_ok] at run
  let initial : Array Row 4#usize :=
    Array.repeat 4#usize (Array.repeat 6#usize field.QM31.ZERO)
  let outerIter : OuterIter := { slice := Array.to_slice initial }
  change
    (do
      let loopOutput ←
        v6_transcript.decode_compact_relation_fields_loop0 fieldsInst
          outerIter (fun iter => iter) fields
      match loopOutput.2.1 with
      | none =>
        ok (.Ok (Array.from_slice initial loopOutput.2.2.slice),
          loopOutput.1)
      | some result => ok (result, loopOutput.1)) =
      ok (.Ok decoded, fieldsOut) at run
  generalize loopRun :
      v6_transcript.decode_compact_relation_fields_loop0 fieldsInst
        outerIter (fun iter => iter) fields = loopResult at run
  cases loopResult with
  | fail error => simp at run
  | div => simp at run
  | ok loopOutput =>
      rcases loopOutput with ⟨fieldsAfter, pending, outerFinal⟩
      cases pending with
      | some pendingResult =>
          cases pendingResult with
          | Err error => simp at run
          | Ok values =>
              exact False.elim
                (successful_outer_relation_field_loop_never_pending_success
                  fieldsInst outerIter (fun iter => iter) fields fieldsAfter
                  (some (.Ok values)) outerFinal loopRun values rfl)
      | none =>
          have finalCanonical := successful_outer_relation_field_loop_canonical
            fieldsInst readCanonical outerIter (fun iter => iter) fields
            fieldsAfter outerFinal 4
            (by
              unfold outerIter initial
              exact repeated_zero_rows_canonical)
            (by
              unfold outerIter initial
              norm_num [Array.to_slice, Array.repeat])
            (by
              intro iter iterLength iterCanonical
              exact ⟨iterCanonical, iterLength⟩)
            loopRun
          simp at run
          rw [← run.1]
          intro rowIndex rowBound
          by_cases correctLength : outerFinal.slice.val.length = 4
          · have finalBound : rowIndex < outerFinal.slice.length := by
              simpa [Array.from_slice, correctLength] using rowBound
            simpa [Array.from_slice, correctLength]
              using finalCanonical rowIndex finalBound
          · have initialBound : rowIndex <
                (Array.to_slice (Array.repeat 4#usize
                  (Array.repeat 6#usize field.QM31.ZERO))).length := by
              simpa [Array.from_slice, correctLength, initial, Array.to_slice,
                Array.repeat] using rowBound
            simpa [Array.from_slice, correctLength, initial, Array.repeat]
              using repeated_zero_rows_canonical rowIndex initialBound

theorem decoded_index_row_canonical
    (decoded : Array Row 4#usize) (row : Row) (ordinal : Std.Usize)
    (ordinalBound : ordinal.val < 4)
    (canonical : DecodedCanonical decoded)
    (read : decoded.index_usize ordinal = ok row) :
    RowCanonical row := by
  have decodedBound : ordinal.val < decoded.val.length := by
    simpa [decoded.property] using ordinalBound
  have selectedCanonical := canonical ordinal.val decodedBound
  unfold Array.index_usize at read
  rw [Array.getElem?_Usize_eq] at read
  rw [List.getElem?_eq_getElem decodedBound] at read
  simp only [Result.ok.injEq] at read
  have selectedExact : decoded.val[ordinal.val] =
      decoded.val[ordinal.val]! :=
    List.Inhabited_getElem_eq_getElem! decoded.val ordinal.val decodedBound
  rw [← selectedExact] at selectedCanonical
  rw [read] at selectedCanonical
  exact selectedCanonical

theorem row_canonical_is_relation_canonical
    (row : Row) (canonical : RowCanonical row) :
    V7CallerCurrentReleaseR26RelationDecodeSemantics.CanonicalRelationRow
      row := by
  intro coefficient coefficientBound
  have rowBound : coefficient < row.val.length := by
    simpa [row.property] using coefficientBound
  have canonicalAt := canonical coefficient rowBound
  rw [← List.Inhabited_getElem_eq_getElem! row.val coefficient rowBound]
    at canonicalAt
  rw [← List.Inhabited_getElem_eq_getElem! row.val coefficient rowBound]
  exact canonicalAt

#print axioms successful_outer_relation_field_loop_canonical
#print axioms successful_outer_relation_field_loop_never_pending_success
#print axioms successful_relation_field_decode_canonical
#print axioms decoded_index_row_canonical
#print axioms row_canonical_is_relation_canonical

end V7CallerCurrentReleaseR30RelationFieldsCanonical
