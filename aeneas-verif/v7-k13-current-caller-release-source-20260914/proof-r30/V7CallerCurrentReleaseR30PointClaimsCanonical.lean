import V7CallerCurrentReleaseR30FixedFieldCanonical
import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Canonicality of decoded point claims

The point-claim decoder fills a fixed 3-by-29 matrix from successful
fixed-field reads.  The proof is structured around exact generated loop
traces and nested-array updates.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30PointClaimsCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace

abbrev RawQM31 := field.QM31
abbrev ClaimRow := Array RawQM31 29#usize
abbrev Claims := Array ClaimRow 3#usize

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩
local instance : Inhabited ClaimRow :=
  ⟨Array.repeat 29#usize field.QM31.ZERO⟩

def CanonicalClaims (claims : Claims) : Prop :=
  ∀ row column, row < 3 → column < 29 →
    GeneratedCanonicalQM31 claims.val[row]!.val[column]!

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem array_index_mut_success
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (back : T → Array T N)
    (run : Array.index_mut_usize values index = ok (value, back)) :
    index.val < N.val ∧ value = values.val[index.val]! ∧
      back = values.set index := by
  unfold Array.index_mut_usize at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨actual, indexRun, run⟩ := run
  unfold Array.index_usize at indexRun
  split at indexRun
  · cases indexRun
  · rename_i present
    have presentList : values.val[index.val]? = some actual := by
      simpa [Result.ok.inj indexRun] using present
    have indexBound : index.val < values.val.length := by
      by_contra outOfBounds
      have absent : values.val[index.val]? = none := by
        exact List.getElem?_eq_none (by omega)
      rw [absent] at presentList
      cases presentList
    have actualExact : actual = values.val[index.val]! := by
      symm
      apply List.getElem!_of_getElem?
      exact presentList
    simp only [Result.ok.injEq, Prod.mk.injEq] at run
    exact ⟨by simpa [Array.length_eq] using indexBound,
      run.1.symm.trans actualExact, run.2.symm⟩

private theorem array_update_success
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values updated : Array T N) (index : Std.Usize) (value : T)
    (run : Array.update values index value = ok updated) :
    index.val < N.val ∧ updated = values.set index value := by
  unfold Array.update at run
  split at run
  · cases run
  · rename_i present
    have presentSome : (values.val[index.val]?).isSome := by
      simpa using congrArg Option.isSome present
    have indexBound : index.val < values.val.length := by
      by_contra outOfBounds
      have absent : values.val[index.val]? = none := by
        exact List.getElem?_eq_none (by omega)
      rw [absent] at presentSome
      cases presentSome
    refine ⟨by simpa [Array.length_eq] using indexBound, ?_⟩
    exact (Result.ok.inj run).symm

private theorem canonical_nested_update
    (claims claimsOut : Claims) (row column : Std.Usize)
    (oldRow updatedRow : ClaimRow) (back : ClaimRow → Claims)
    (value : RawQM31)
    (indexRun : Array.index_mut_usize claims row = ok (oldRow, back))
    (updateRun : Array.update oldRow column value = ok updatedRow)
    (claimsExact : claimsOut = back updatedRow)
    (canonical : CanonicalClaims claims)
    (valueCanonical : GeneratedCanonicalQM31 value) :
    CanonicalClaims claimsOut := by
  obtain ⟨rowBound, oldRowExact, backExact⟩ :=
    array_index_mut_success claims row oldRow back indexRun
  obtain ⟨columnBound, updatedExact⟩ :=
    array_update_success oldRow updatedRow column value updateRun
  rw [claimsExact, backExact, updatedExact, oldRowExact]
  intro targetRow targetColumn targetRowBound targetColumnBound
  by_cases sameRow : targetRow = row.val
  · subst targetRow
    rw [Array.set_val_eq]
    rw [List.set_getElem!_eq _ _ _ _ ⟨by
      simpa [Array.length_eq] using rowBound, rfl⟩]
    by_cases sameColumn : targetColumn = column.val
    · subst targetColumn
      rw [Array.set_val_eq]
      rw [List.set_getElem!_eq _ _ _ _ ⟨by
        simpa [Array.length_eq] using columnBound, rfl⟩]
      exact valueCanonical
    · rw [Array.set_val_eq]
      rw [List.set_getElem!_ne _ _ _ _ (by omega)]
      exact canonical row.val targetColumn rowBound targetColumnBound
  · rw [Array.set_val_eq]
    rw [List.set_getElem!_ne _ _ _ _ (by omega)]
    exact canonical targetRow targetColumn targetRowBound targetColumnBound

abbrev Encoded := alloc.vec.Vec Std.U8
abbrev InnerState (Fields : Type) :=
  core.ops.range.Range Std.Usize × Fields × Claims × Encoded
abbrev InnerOutput (Fields : Type) := Fields × Claims × Encoded ×
  Option (core.result.Result Claims v6_transcript.V6TranscriptError)

def innerBody {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (columnCount row : Std.Usize) (state : InnerState Fields) :
    Result (ControlFlow (InnerState Fields) (InnerOutput Fields)) :=
  v6_transcript.decode_and_absorb_point_claims_loop0_loop0.body fieldsInst
    columnCount row state.1 state.2.1 state.2.2.1 state.2.2.2

private theorem branch_eq_ok_of_continue {Value Error : Type}
    (result : core.result.Result Value Error) (value : Value)
    (success : core.result.Result.Insts.CoreOpsTry.branch result =
      ok (.Continue value)) :
    result = .Ok value := by
  cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at success ⊢
  exact success

private theorem continuing_inner_preserves
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (columnCount row : Std.Usize) (state next : InnerState Fields)
    (edge : innerBody fieldsInst columnCount row state = ok (cont next))
    (canonical : CanonicalClaims state.2.2.1) :
    CanonicalClaims next.2.2.1 := by
  rcases state with ⟨iter, fields, claims, encoded⟩
  rcases next with ⟨iterOut, fieldsOut, claimsOut, encodedOut⟩
  change CanonicalClaims claims at canonical
  change CanonicalClaims claimsOut
  unfold innerBody at edge
  unfold v6_transcript.decode_and_absorb_point_claims_loop0_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none => cases edge
  | some column =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨rowOffset, rowOffsetRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨ordinal, ordinalRun, edge⟩ := edge
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
          obtain ⟨rowPair, rowRun, edge⟩ := edge
          rcases rowPair with ⟨oldRow, rowBack⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨updatedRow, updateRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨byteOffset, byteOffsetRun, edge⟩ := edge
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
          exact canonical_nested_update claims claimsOut row column oldRow
            updatedRow rowBack value rowRun updateRun edge.2.2.1.symm
            canonical valueCanonical

private theorem done_inner_preserves
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (columnCount row : Std.Usize) (state : InnerState Fields)
    (output : InnerOutput Fields)
    (edge : innerBody fieldsInst columnCount row state = ok (done output))
    (canonical : CanonicalClaims state.2.2.1) :
    CanonicalClaims output.2.1 := by
  rcases state with ⟨iter, fields, claims, encoded⟩
  change CanonicalClaims claims at canonical
  unfold innerBody at edge
  unfold v6_transcript.decode_and_absorb_point_claims_loop0_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      rw [← ControlFlow.done.inj (Result.ok.inj edge)]
      exact canonical
  | some column =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨rowOffset, rowOffsetRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨ordinal, ordinalRun, edge⟩ := edge
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
              all_goals exact canonical
      | Continue value =>
          simp only at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨rowPair, rowRun, edge⟩ := edge
          rcases rowPair with ⟨oldRow, rowBack⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨updatedRow, updateRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨byteOffset, byteOffsetRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨slicePair, sliceRun, edge⟩ := edge
          rcases slicePair with ⟨slice, sliceBack⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨prefixPair, prefixRun, edge⟩ := edge
          rcases prefixPair with ⟨prefixSlice, prefixBack⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨written, writeRun, edge⟩ := edge
          cases edge

private theorem inner_trace_preserves
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (columnCount row : Std.Usize) {state : InnerState Fields}
    {output : InnerOutput Fields}
    (trace : ExactLoopTrace (innerBody fieldsInst columnCount row) state output)
    (canonical : CanonicalClaims state.2.2.1) :
    CanonicalClaims output.2.1 := by
  induction trace with
  | done edge =>
      exact done_inner_preserves fieldsInst columnCount row _ _ edge canonical
  | @cont _ next _ edge tail inductionHypothesis =>
      exact inductionHypothesis
        (continuing_inner_preserves fieldsInst readCanonical columnCount row _
          next edge canonical)

theorem successful_point_claims_inner_loop_preserves
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (columnCount row : Std.Usize)
    (iter : core.ops.range.Range Std.Usize)
    (fields fieldsOut : Fields) (claims claimsOut : Claims)
    (encoded encodedOut : Encoded)
    (pending : Option (core.result.Result Claims
      v6_transcript.V6TranscriptError))
    (canonical : CanonicalClaims claims)
    (run : v6_transcript.decode_and_absorb_point_claims_loop0_loop0
      fieldsInst columnCount iter fields claims encoded row =
        ok (fieldsOut, claimsOut, encodedOut, pending)) :
    CanonicalClaims claimsOut := by
  unfold v6_transcript.decode_and_absorb_point_claims_loop0_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace
    (innerBody fieldsInst columnCount row) (iter, fields, claims, encoded)
    (fieldsOut, claimsOut, encodedOut, pending) run
  exact inner_trace_preserves fieldsInst readCanonical columnCount row trace
    canonical

private theorem done_inner_never_pending_success
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (columnCount row : Std.Usize) (state : InnerState Fields)
    (output : InnerOutput Fields)
    (edge : innerBody fieldsInst columnCount row state = ok (done output)) :
    ∀ values : Claims, output.2.2.2 ≠ some (.Ok values) := by
  rcases state with ⟨iter, fields, claims, encoded⟩
  unfold innerBody at edge
  unfold v6_transcript.decode_and_absorb_point_claims_loop0_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      rw [← ControlFlow.done.inj (Result.ok.inj edge)]
      intro values
      simp
  | some column =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨rowOffset, rowOffsetRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨ordinal, ordinalRun, edge⟩ := edge
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
              all_goals intro values
              all_goals simp
      | Continue value =>
          simp only at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨rowPair, rowRun, edge⟩ := edge
          rcases rowPair with ⟨oldRow, rowBack⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨updatedRow, updateRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨byteOffset, byteOffsetRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨slicePair, sliceRun, edge⟩ := edge
          rcases slicePair with ⟨slice, sliceBack⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨prefixPair, prefixRun, edge⟩ := edge
          rcases prefixPair with ⟨prefixSlice, prefixBack⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨written, writeRun, edge⟩ := edge
          cases edge

private theorem inner_trace_never_pending_success
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (columnCount row : Std.Usize) {state : InnerState Fields}
    {output : InnerOutput Fields}
    (trace : ExactLoopTrace (innerBody fieldsInst columnCount row) state output) :
    ∀ values : Claims, output.2.2.2 ≠ some (.Ok values) := by
  induction trace with
  | done edge =>
      exact done_inner_never_pending_success fieldsInst columnCount row _ _ edge
  | cont edge tail inductionHypothesis => exact inductionHypothesis

theorem successful_point_claims_inner_loop_never_pending_success
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (columnCount row : Std.Usize)
    (iter : core.ops.range.Range Std.Usize)
    (fields fieldsOut : Fields) (claims claimsOut : Claims)
    (encoded encodedOut : Encoded)
    (pending : Option (core.result.Result Claims
      v6_transcript.V6TranscriptError))
    (run : v6_transcript.decode_and_absorb_point_claims_loop0_loop0
      fieldsInst columnCount iter fields claims encoded row =
        ok (fieldsOut, claimsOut, encodedOut, pending)) :
    ∀ values : Claims, pending ≠ some (.Ok values) := by
  unfold v6_transcript.decode_and_absorb_point_claims_loop0_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace
    (innerBody fieldsInst columnCount row) (iter, fields, claims, encoded)
    (fieldsOut, claimsOut, encodedOut, pending) run
  exact inner_trace_never_pending_success fieldsInst columnCount row trace

abbrev OuterState (Fields : Type) := InnerState Fields
abbrev OuterOutput (Fields : Type) := InnerOutput Fields

def outerBody {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (columnCount : Std.Usize) (state : OuterState Fields) :
    Result (ControlFlow (OuterState Fields) (OuterOutput Fields)) :=
  v6_transcript.decode_and_absorb_point_claims_loop0.body fieldsInst
    columnCount state.1 state.2.1 state.2.2.1 state.2.2.2

private theorem continuing_outer_preserves
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (columnCount : Std.Usize) (state next : OuterState Fields)
    (edge : outerBody fieldsInst columnCount state = ok (cont next))
    (canonical : CanonicalClaims state.2.2.1) :
    CanonicalClaims next.2.2.1 := by
  rcases state with ⟨iter, fields, claims, encoded⟩
  rcases next with ⟨iterOut, fieldsOut, claimsOut, encodedOut⟩
  change CanonicalClaims claims at canonical
  change CanonicalClaims claimsOut
  unfold outerBody at edge
  unfold v6_transcript.decode_and_absorb_point_claims_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none => cases edge
  | some row =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨innerOut, innerRun, edge⟩ := edge
      rcases innerOut with ⟨fieldsAfter, claimsAfter, encodedAfter, pending⟩
      have innerCanonical := successful_point_claims_inner_loop_preserves
        fieldsInst readCanonical columnCount row
        { start := 0#usize, «end» := columnCount }
        fields fieldsAfter claims claimsAfter encoded encodedAfter pending
        canonical innerRun
      cases pending with
      | some pendingResult => cases edge
      | none =>
          simp only [Result.ok.injEq, ControlFlow.cont.injEq,
            Prod.mk.injEq] at edge
          rw [← edge.2.2.1]
          exact innerCanonical

private theorem done_outer_facts
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (columnCount : Std.Usize) (state : OuterState Fields)
    (output : OuterOutput Fields)
    (edge : outerBody fieldsInst columnCount state = ok (done output))
    (canonical : CanonicalClaims state.2.2.1) :
    CanonicalClaims output.2.1 ∧
      ∀ values : Claims, output.2.2.2 ≠ some (.Ok values) := by
  rcases state with ⟨iter, fields, claims, encoded⟩
  change CanonicalClaims claims at canonical
  unfold outerBody at edge
  unfold v6_transcript.decode_and_absorb_point_claims_loop0.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      rw [← ControlFlow.done.inj (Result.ok.inj edge)]
      exact ⟨canonical, by intro values; simp⟩
  | some row =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨innerOut, innerRun, edge⟩ := edge
      rcases innerOut with ⟨fieldsAfter, claimsAfter, encodedAfter, pending⟩
      have innerCanonical := successful_point_claims_inner_loop_preserves
        fieldsInst readCanonical columnCount row
        { start := 0#usize, «end» := columnCount }
        fields fieldsAfter claims claimsAfter encoded encodedAfter pending
        canonical innerRun
      have innerNever :=
        successful_point_claims_inner_loop_never_pending_success fieldsInst
          columnCount row { start := 0#usize, «end» := columnCount }
          fields fieldsAfter claims claimsAfter encoded encodedAfter pending
          innerRun
      cases pending with
      | none => cases edge
      | some pendingResult =>
          cases pendingResult with
          | Ok values => exact False.elim (innerNever values rfl)
          | Err error =>
              rw [← ControlFlow.done.inj (Result.ok.inj edge)]
              exact ⟨innerCanonical, by intro values; simp⟩

private theorem outer_trace_facts
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (columnCount : Std.Usize) {state : OuterState Fields}
    {output : OuterOutput Fields}
    (trace : ExactLoopTrace (outerBody fieldsInst columnCount) state output)
    (canonical : CanonicalClaims state.2.2.1) :
    CanonicalClaims output.2.1 ∧
      ∀ values : Claims, output.2.2.2 ≠ some (.Ok values) := by
  induction trace with
  | done edge =>
      exact done_outer_facts fieldsInst readCanonical columnCount _ _ edge
        canonical
  | @cont _ next _ edge tail inductionHypothesis =>
      exact inductionHypothesis
        (continuing_outer_preserves fieldsInst readCanonical columnCount _ next
          edge canonical)

theorem successful_point_claims_outer_loop_facts
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (columnCount : Std.Usize) (iter : core.ops.range.Range Std.Usize)
    (fields fieldsOut : Fields) (claims claimsOut : Claims)
    (encoded encodedOut : Encoded)
    (pending : Option (core.result.Result Claims
      v6_transcript.V6TranscriptError))
    (canonical : CanonicalClaims claims)
    (run : v6_transcript.decode_and_absorb_point_claims_loop0 fieldsInst
      columnCount iter fields claims encoded =
        ok (fieldsOut, claimsOut, encodedOut, pending)) :
    CanonicalClaims claimsOut ∧
      ∀ values : Claims, pending ≠ some (.Ok values) := by
  unfold v6_transcript.decode_and_absorb_point_claims_loop0 at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace
    (outerBody fieldsInst columnCount) (iter, fields, claims, encoded)
    (fieldsOut, claimsOut, encodedOut, pending) run
  exact outer_trace_facts fieldsInst readCanonical columnCount trace canonical

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

private theorem repeated_zero_claims_canonical :
    CanonicalClaims
      (Array.repeat 3#usize (Array.repeat 29#usize field.QM31.ZERO)) := by
  intro row column rowBound columnBound
  let rows : Std.Usize := 3#usize
  let columns : Std.Usize := 29#usize
  change GeneratedCanonicalQM31
    (getElem! (getElem! (Array.repeat rows
      (Array.repeat columns field.QM31.ZERO)).val row).val column)
  have rowExact := array_repeat_getElemBang rows
    (Array.repeat columns field.QM31.ZERO) row (by
      simpa [rows] using rowBound)
  rw [rowExact]
  have columnExact := array_repeat_getElemBang columns field.QM31.ZERO column
    (by simpa [columns] using columnBound)
  rw [columnExact]
  exact zero_canonical

theorem successful_decode_and_absorb_point_claims_canonical
    {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (readCanonical : ∀ fields value fieldsNext,
      fieldsInst.next_qm31 fields = ok (.Ok value, fieldsNext) →
        GeneratedCanonicalQM31 value)
    (transcriptIn transcriptOut : transcript.Transcript)
    (fields fieldsOut : Fields) (claims : Claims)
    (run : v6_transcript.decode_and_absorb_point_claims fieldsInst
      transcriptIn fields = ok (.Ok claims, transcriptOut, fieldsOut)) :
    CanonicalClaims claims := by
  unfold v6_transcript.decode_and_absorb_point_claims at run
  simp only at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨columnCount, columnCountRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨claimCount, claimCountRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨encodedLength, encodedLengthRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨encoded, encodedRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨loopOut, loopRun, run⟩ := run
  rcases loopOut with ⟨fieldsAfter, claimsAfter, encodedAfter, pending⟩
  have loopFacts := successful_point_claims_outer_loop_facts fieldsInst
    readCanonical columnCount
    { start := 0#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS }
    fields fieldsAfter
    (Array.repeat 3#usize (Array.repeat 29#usize field.QM31.ZERO))
    claimsAfter encoded encodedAfter pending repeated_zero_claims_canonical loopRun
  cases pending with
  | some pendingResult =>
      cases pendingResult with
      | Err error => simp at run
      | Ok values =>
          exact False.elim (loopFacts.2 values rfl)
  | none =>
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨transcriptAfter, absorbRun, run⟩ := run
      have outputExact := Result.ok.inj run
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at outputExact
      rw [← outputExact.1]
      exact loopFacts.1

theorem fixed_reader_point_claims_canonical
    (transcriptIn transcriptOut : transcript.Transcript)
    (reader readerOut : v6_onefold.V6FixedFieldReader)
    (claims : Claims)
    (run : v6_transcript.decode_and_absorb_point_claims
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
      transcriptIn reader = ok (.Ok claims, transcriptOut, readerOut)) :
    CanonicalClaims claims := by
  exact successful_decode_and_absorb_point_claims_canonical
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    (fun current value next success =>
      V7CallerCurrentReleaseR30FixedFieldCanonical.fixed_reader_next_qm31_canonical
        current next value success)
    transcriptIn transcriptOut reader readerOut claims run

#print axioms canonical_nested_update
#print axioms successful_point_claims_inner_loop_preserves
#print axioms successful_point_claims_inner_loop_never_pending_success
#print axioms successful_point_claims_outer_loop_facts
#print axioms successful_decode_and_absorb_point_claims_canonical
#print axioms fixed_reader_point_claims_canonical

end V7CallerCurrentReleaseR30PointClaimsCanonical
