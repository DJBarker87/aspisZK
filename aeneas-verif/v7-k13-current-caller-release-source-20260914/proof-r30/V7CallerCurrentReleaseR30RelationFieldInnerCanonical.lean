import V7CallerCurrentReleaseR30FixedFieldCanonical
import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Canonicality through one relation-field decoder row

This module proves the inner generated decoder loop preserves canonicality as
it fills one six-element relation row.  The proof is symbolic over the loop
trace and assumes only that successful stream reads are canonical.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30RelationFieldInnerCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace

abbrev RawQM31 := field.QM31
abbrev Iter := core.slice.iter.IterMut RawQM31

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def CanonicalSlice (values : Slice RawQM31) : Prop :=
  ∀ index, index < values.length →
    GeneratedCanonicalQM31 values.val[index]!

def BackPreservesCanonical (length : Nat) (back : Iter → Iter) : Prop :=
  ∀ iter, iter.slice.length = length → CanonicalSlice iter.slice →
    CanonicalSlice (back iter).slice ∧ (back iter).slice.length = length

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem canonical_slice_set
    (values : Slice RawQM31) (index : Nat) (value : RawQM31)
    (active : index < values.length)
    (canonical : CanonicalSlice values)
    (valueCanonical : GeneratedCanonicalQM31 value) :
    CanonicalSlice (values.setAtNat index value) := by
  intro target targetBound
  have oldTargetBound : target < values.length := by
    simpa [Slice.setAtNat] using targetBound
  by_cases same : target = index
  · subst target
    simpa [Slice.setAtNat, List.getElem!_eq_getElem?_getD, active]
      using valueCanonical
  · have oldCanonical := canonical target oldTargetBound
    simpa [Slice.setAtNat, active, List.getElem!_eq_getElem?_getD, same]
      using oldCanonical

private theorem iterator_some_preserves_slice
    (iter iterNext : Iter) (nextBack : Iter → Option RawQM31 → Iter)
    (value : RawQM31)
    (run : core.slice.iter.IteratorIterMut.next iter =
      ok (some value, iterNext, nextBack)) :
    iterNext.slice = iter.slice := by
  unfold core.slice.iter.IteratorIterMut.next at run
  split at run <;> simp_all
  rw [← run.2.1]

private theorem iterator_some_back_preserves
    (iter iterNext : Iter) (nextBack : Iter → Option RawQM31 → Iter)
    (oldValue value : RawQM31)
    (run : core.slice.iter.IteratorIterMut.next iter =
      ok (some oldValue, iterNext, nextBack))
    (valueCanonical : GeneratedCanonicalQM31 value)
    (length : Nat) (iterLength : iter.slice.length = length) :
    ∀ candidate, candidate.slice.length = length →
      CanonicalSlice candidate.slice →
      CanonicalSlice (nextBack candidate (some value)).slice ∧
        (nextBack candidate (some value)).slice.length = length := by
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
    · exact canonical_slice_set candidate.slice iter.i value activeCandidate
        candidateCanonical valueCanonical
    · simpa [Slice.setAtNat] using candidateLength
  · simp at run

private theorem iterator_none_back_preserves
    (iter iterNext : Iter) (nextBack : Iter → Option RawQM31 → Iter)
    (run : core.slice.iter.IteratorIterMut.next iter =
      ok (none, iterNext, nextBack))
    (canonical : CanonicalSlice iter.slice) (length : Nat)
    (iterLength : iter.slice.length = length) :
    CanonicalSlice (nextBack iterNext none).slice ∧
      (nextBack iterNext none).slice.length = length := by
  unfold core.slice.iter.IteratorIterMut.next at run
  split at run
  · simp at run
  · simp only [Result.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨_, iterExact, backExact⟩
    rw [← iterExact, ← backExact]
    exact ⟨canonical, iterLength⟩

abbrev InnerState (Fields : Type) := Iter × (Iter → Iter) × Fields
abbrev InnerOutput (Fields : Type) :=
  Fields × (Option (core.result.Result
    (Array (Array RawQM31 6#usize) 4#usize)
    v6_transcript.V6TranscriptError)) × Iter

structure InnerStep {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (state next : InnerState Fields) : Type where
  oldValue : RawQM31
  value : RawQM31
  nextBack : Iter → Option RawQM31 → Iter
  iteratorSuccess :
    core.slice.iter.IteratorIterMut.next state.1 =
      ok (some oldValue, next.1, nextBack)
  readSuccess :
    fieldsInst.next_qm31 state.2.2 = ok (.Ok value, next.2.2)
  backExact :
    next.2.1 = fun iter => state.2.1 (nextBack iter (some value))

private theorem continuing_body_exposes_step
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (state next : InnerState Fields)
    (edge :
      v6_transcript.decode_compact_relation_fields_loop0_loop0.body
          fieldsInst state.1 state.2.1 state.2.2 = ok (cont next)) :
    Nonempty (InnerStep fieldsInst state next) := by
  rcases state with ⟨iter, back, fields⟩
  rcases next with ⟨iterNext, backNext, fieldsNext⟩
  unfold v6_transcript.decode_compact_relation_fields_loop0_loop0.body at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorTriple, iteratorRun, edge⟩ := edge
  rcases iteratorTriple with ⟨option, iterAfter, nextBack⟩
  cases option with
  | none => cases edge
  | some oldValue =>
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
          have readExact : readResult = .Ok value := by
            cases readResult <;>
              simp [core.result.Result.Insts.CoreOpsTry.branch] at branchRun
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using branchRun
          subst readResult
          simp only [Result.ok.injEq, ControlFlow.cont.injEq,
            Prod.mk.injEq] at edge
          rcases edge with ⟨iterExact, backExact, fieldsExact⟩
          subst iterAfter
          subst fieldsAfter
          exact ⟨{
            oldValue := oldValue
            value := value
            nextBack := nextBack
            iteratorSuccess := iteratorRun
            readSuccess := readRun
            backExact := backExact.symm }⟩

private theorem done_none_exposes_iterator
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (state : InnerState Fields) (output : InnerOutput Fields)
    (pendingNone : output.2.1 = none)
    (edge :
      v6_transcript.decode_compact_relation_fields_loop0_loop0.body
          fieldsInst state.1 state.2.1 state.2.2 = ok (done output)) :
    ∃ iterAfter nextBack,
      core.slice.iter.IteratorIterMut.next state.1 =
        ok (none, iterAfter, nextBack) ∧
      output = (state.2.2, none, state.2.1 (nextBack iterAfter none)) := by
  rcases state with ⟨iter, back, fields⟩
  unfold v6_transcript.decode_compact_relation_fields_loop0_loop0.body at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorTriple, iteratorRun, edge⟩ := edge
  rcases iteratorTriple with ⟨option, iterAfter, nextBack⟩
  cases option with
  | none =>
      refine ⟨iterAfter, nextBack, iteratorRun, ?_⟩
      exact (ControlFlow.done.inj (Result.ok.inj edge)).symm
  | some oldValue =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨readPair, readRun, edge⟩ := edge
      rcases readPair with ⟨readResult, fieldsAfter⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨flow, branchRun, edge⟩ := edge
      cases flow with
      | Continue value => cases edge
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
              all_goals simp at pendingNone

private theorem done_pending_classification
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (state : InnerState Fields) (output : InnerOutput Fields)
    (edge :
      v6_transcript.decode_compact_relation_fields_loop0_loop0.body
          fieldsInst state.1 state.2.1 state.2.2 = ok (done output)) :
    output.2.1 = none ∨
      ∃ error : v6_transcript.V6TranscriptError,
        output.2.1 = some (.Err error) := by
  rcases state with ⟨iter, back, fields⟩
  unfold v6_transcript.decode_compact_relation_fields_loop0_loop0.body at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorTriple, iteratorRun, edge⟩ := edge
  rcases iteratorTriple with ⟨option, iterAfter, nextBack⟩
  cases option with
  | none =>
      have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
      rw [← outputExact]
      exact Or.inl rfl
  | some oldValue =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨readPair, readRun, edge⟩ := edge
      rcases readPair with ⟨readResult, fieldsAfter⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨flow, branchRun, edge⟩ := edge
      cases flow with
      | Continue value => cases edge
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
              all_goals right
              all_goals exact ⟨_, rfl⟩

private theorem exact_trace_never_returns_pending_success
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    {state : InnerState Fields} {output : InnerOutput Fields}
    (trace : ExactLoopTrace
      (fun state : InnerState Fields =>
        v6_transcript.decode_compact_relation_fields_loop0_loop0.body
          fieldsInst state.1 state.2.1 state.2.2)
      state output) :
    ∀ values : Array (Array RawQM31 6#usize) 4#usize,
      output.2.1 ≠ some (.Ok values) := by
  induction trace with
  | done edge =>
      rcases done_pending_classification fieldsInst _ _ edge with
        pendingNone | ⟨error, pendingError⟩
      · intro values pendingSuccess
        rw [pendingNone] at pendingSuccess
        simp at pendingSuccess
      · intro values pendingSuccess
        rw [pendingError] at pendingSuccess
        simp at pendingSuccess
  | cont edge tail inductionHypothesis => exact inductionHypothesis

theorem successful_inner_relation_field_loop_never_pending_success
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (iter : Iter) (back : Iter → Iter) (fields fieldsOut : Fields)
    (pending : Option (core.result.Result
      (Array (Array RawQM31 6#usize) 4#usize)
      v6_transcript.V6TranscriptError))
    (backOut : Iter)
    (run :
      v6_transcript.decode_compact_relation_fields_loop0_loop0 fieldsInst
          iter back fields = ok (fieldsOut, pending, backOut)) :
    ∀ values, pending ≠ some (.Ok values) := by
  unfold v6_transcript.decode_compact_relation_fields_loop0_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace
    (fun state : InnerState Fields =>
      v6_transcript.decode_compact_relation_fields_loop0_loop0.body
        fieldsInst state.1 state.2.1 state.2.2)
    (iter, back, fields) (fieldsOut, pending, backOut) run
  exact exact_trace_never_returns_pending_success fieldsInst trace

private theorem exact_trace_returns_canonical
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value) :
    ∀ (length : Nat) {state output},
      ExactLoopTrace
        (fun state : InnerState Fields =>
          v6_transcript.decode_compact_relation_fields_loop0_loop0.body
            fieldsInst state.1 state.2.1 state.2.2)
        state output →
      CanonicalSlice state.1.slice →
      state.1.slice.length = length →
      BackPreservesCanonical length state.2.1 →
      output.2.1 = none →
      CanonicalSlice output.2.2.slice := by
  intro length state output trace iterCanonical iterLength backPreserves
    pendingNone
  cases trace with
  | done edge =>
      obtain ⟨iterAfter, nextBack, iteratorRun, outputExact⟩ :=
        done_none_exposes_iterator fieldsInst state output pendingNone edge
      rw [outputExact]
      obtain ⟨nextCanonical, nextLength⟩ :=
        iterator_none_back_preserves state.1 iterAfter nextBack iteratorRun
          iterCanonical length iterLength
      exact (backPreserves _ nextLength nextCanonical).1
  | @cont _ next _ edge tail =>
      obtain ⟨step⟩ := continuing_body_exposes_step fieldsInst state next edge
      have valueCanonical := readCanonical state.2.2 step.value next.2.2
        step.readSuccess
      have nextIterCanonical : CanonicalSlice next.1.slice := by
        rw [iterator_some_preserves_slice state.1 next.1 step.nextBack
          step.oldValue step.iteratorSuccess]
        exact iterCanonical
      have nextIterLength : next.1.slice.length = length := by
        rw [iterator_some_preserves_slice state.1 next.1 step.nextBack
          step.oldValue step.iteratorSuccess]
        exact iterLength
      have nextBackPreserves : BackPreservesCanonical length next.2.1 := by
        rw [step.backExact]
        intro candidate candidateLength candidateCanonical
        obtain ⟨updatedCanonical, updatedLength⟩ :=
          iterator_some_back_preserves state.1 next.1 step.nextBack
            step.oldValue step.value step.iteratorSuccess valueCanonical
            length iterLength candidate candidateLength candidateCanonical
        exact backPreserves _ updatedLength updatedCanonical
      exact exact_trace_returns_canonical fieldsInst readCanonical length tail
        nextIterCanonical nextIterLength nextBackPreserves pendingNone

theorem successful_inner_relation_field_loop_canonical
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (iter : Iter) (back : Iter → Iter) (fields fieldsOut : Fields)
    (backOut : Iter)
    (length : Nat)
    (iterCanonical : CanonicalSlice iter.slice)
    (iterLength : iter.slice.length = length)
    (backPreserves : BackPreservesCanonical length back)
    (run :
      v6_transcript.decode_compact_relation_fields_loop0_loop0 fieldsInst
          iter back fields = ok (fieldsOut, none, backOut)) :
    CanonicalSlice backOut.slice := by
  unfold v6_transcript.decode_compact_relation_fields_loop0_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace
    (fun state : InnerState Fields =>
      v6_transcript.decode_compact_relation_fields_loop0_loop0.body
        fieldsInst state.1 state.2.1 state.2.2)
    (iter, back, fields) (fieldsOut, none, backOut) run
  exact exact_trace_returns_canonical fieldsInst readCanonical length trace
    iterCanonical iterLength backPreserves rfl

#print axioms successful_inner_relation_field_loop_canonical
#print axioms successful_inner_relation_field_loop_never_pending_success

end V7CallerCurrentReleaseR30RelationFieldInnerCanonical
