import V7CallerCurrentReleaseR26PreparedSum3Semantics
import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Exact semantics of the current in-place value-prefix fold

The production relation tail stores every later coefficient layer in one
256-entry array.  Each iteration reads one untouched four-entry fibre and
writes its natural-basis fold into the compacted prefix.  This file proves the
generic loop invariant once, including the source's prepared three-product
helper, and exposes the exact `n * 4 -> n` prefix semantics used at sizes
`256`, `64`, and `16`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26FoldValuesPrefixSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26PreparedSumSemantics
open V7CallerCurrentReleaseR26PreparedSum3Semantics
open V7CallerCurrentReleaseR26AcceptedTailTrace

abbrev RawQM31 := field.QM31
abbrev RawPrepared := field.PreparedQm31Multiplier
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩
local instance : Inhabited RawPrepared :=
  ⟨⟨Array.repeat 3#usize (Array.repeat 3#usize 0#u32)⟩⟩

abbrev FoldState :=
  core.ops.range.Range Std.Usize × Array RawQM31 256#usize

def CanonicalValues (values : Array RawQM31 256#usize) : Prop :=
  ∀ index, index < 256 → GeneratedCanonicalQM31 values.val[index]!

def exactValueAt (values : Array RawQM31 256#usize) (index : Nat) : ExactQM31 :=
  generatedQm31ToExact values.val[index]!

def coefficientFoldAt
    (values : Array RawQM31 256#usize) (alpha : ExactQM31)
    (fibre : Nat) : ExactQM31 :=
  exactValueAt values (4 * fibre) +
    alpha * exactValueAt values (4 * fibre + 1) +
    alpha ^ 2 * exactValueAt values (4 * fibre + 2) +
    alpha ^ 3 * exactValueAt values (4 * fibre + 3)

def FoldPrefixInvariant
    (base current : Array RawQM31 256#usize)
    (alpha : ExactQM31) (processed limit : Nat) : Prop :=
  CanonicalValues current ∧
    processed ≤ limit ∧ limit ≤ 64 ∧
    (∀ fibre, fibre < processed →
      exactValueAt current fibre = coefficientFoldAt base alpha fibre) ∧
    ∀ index, processed ≤ index → index < 256 →
      current.val[index]! = base.val[index]!

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem arrayIndexRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have listEq : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simp
  simpa [valueEq, listEq] using run

private theorem arrayUpdateEqSet
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values updated : Array T N) (index : Std.Usize) (value : T)
    (hindex : index.val < N.val)
    (run : Array.update values index value = ok updated) :
    updated = values.set index value := by
  obtain ⟨expected, expectedRun, expectedEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value (by
      simpa [Array.length_eq] using hindex))
  have outputEq : updated = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  exact outputEq.trans expectedEq

private theorem arraySetSame
    (values : Array RawQM31 256#usize) (index : Std.Usize)
    (value : RawQM31) (hindex : index.val < 256) :
    (values.set index value).val[index.val]! = value := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_eq
  exact ⟨by simpa [Array.length_eq] using hindex, rfl⟩

private theorem arraySetNe
    (values : Array RawQM31 256#usize) (index : Std.Usize)
    (value : RawQM31) (other : Nat) (hne : other ≠ index.val) :
    (values.set index value).val[other]! = values.val[other]! := by
  apply List.set_getElem!_ne
  omega

private theorem canonicalSet
    (values : Array RawQM31 256#usize) (index : Std.Usize)
    (value : RawQM31) (hindex : index.val < 256)
    (hvalues : CanonicalValues values)
    (hvalue : GeneratedCanonicalQM31 value) :
    CanonicalValues (values.set index value) := by
  intro other hother
  by_cases hsame : other = index.val
  · subst other
    rw [arraySetSame values index value hindex]
    exact hvalue
  · rw [arraySetNe values index value other hsame]
    exact hvalues other hother

private theorem wrappingMulFourExact
    (index : Std.Usize) (hindex : index.val < 64) :
    (Std.Usize.wrapping_mul 4#usize index).val = 4 * index.val := by
  rw [Std.Usize.wrapping_mul_val_eq]
  simp only [UScalar.ofNatCore_val_eq]
  have hsize : 256 < Usize.size := by
    have literalBound := (257#usize).hSize
    scalar_tac
  rw [Nat.mod_eq_of_lt (by
    simpa [UScalar.size_UScalarTyUsize] using
      (show 4 * index.val < Usize.size by omega))]

private theorem wrappingAddSmallExact
    (offset delta : Std.Usize)
    (hbound : offset.val + delta.val < 256) :
    (Std.Usize.wrapping_add offset delta).val = offset.val + delta.val := by
  rw [Std.Usize.wrapping_add_val_eq]
  have hsize : 256 < Usize.size := by
    have literalBound := (257#usize).hSize
    scalar_tac
  rw [Nat.mod_eq_of_lt (by
    simpa [UScalar.size_UScalarTyUsize] using
      (show offset.val + delta.val < Usize.size by omega))]

/-- Literal values and calls exposed by one continuing generated loop edge. -/
structure ExactFoldStep
    (prepared : Array RawPrepared 3#usize)
    (state nextState : FoldState) : Type where
  index : Std.Usize
  offset : Std.Usize
  offset1 : Std.Usize
  offset2 : Std.Usize
  offset3 : Std.Usize
  q : RawQM31
  q1 : RawQM31
  q2 : RawQM31
  q3 : RawQM31
  q4 : RawQM31
  iteratorSuccess :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
      ok (some index, nextState.1)
  offsetSuccess : Std.Usize.wrapping_mul 4#usize index = offset
  qSuccess : state.2.index_usize offset = ok q
  offset1Success : Std.Usize.wrapping_add offset 1#usize = offset1
  q1Success : state.2.index_usize offset1 = ok q1
  offset2Success : Std.Usize.wrapping_add offset 2#usize = offset2
  q2Success : state.2.index_usize offset2 = ok q2
  offset3Success : Std.Usize.wrapping_add offset 3#usize = offset3
  q3Success : state.2.index_usize offset3 = ok q3
  sumSuccess :
    field.qm31_add_sum_products3_prepared q prepared
      (Array.make 3#usize [q1, q2, q3]) = ok q4
  updateSuccess : state.2.update index q4 = ok nextState.2

private theorem continuingBodyExposesStep
    (prepared : Array RawPrepared 3#usize)
    (state nextState : FoldState)
    (edge : v6_transcript.fold_values_prefix_loop.body
      prepared state.1 state.2 = ok (cont nextState)) :
    Nonempty (ExactFoldStep prepared state nextState) := by
  rcases state with ⟨iter, values⟩
  rcases nextState with ⟨iterNext, valuesNext⟩
  unfold v6_transcript.fold_values_prefix_loop.body at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, hiterator, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none => cases edge
  | some index =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨offset, hoffset, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨q, hq, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨offset1, hoffset1, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨q1, hq1, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨offset2, hoffset2, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨q2, hq2, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨offset3, hoffset3, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨q3, hq3, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨q4, hsum, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨updated, hupdate, edge⟩ := edge
      simp only [Aeneas.Std.Result.ok.injEq,
        Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq] at edge
      rcases edge with ⟨iterExact, valuesExact⟩
      subst iterAfter
      subst updated
      exact ⟨{
        index := index
        offset := offset
        offset1 := offset1
        offset2 := offset2
        offset3 := offset3
        q := q
        q1 := q1
        q2 := q2
        q3 := q3
        q4 := q4
        iteratorSuccess := hiterator
        offsetSuccess := by simpa [lift] using hoffset
        qSuccess := hq
        offset1Success := by simpa [lift] using hoffset1
        q1Success := hq1
        offset2Success := by simpa [lift] using hoffset2
        q2Success := hq2
        offset3Success := by simpa [lift] using hoffset3
        q3Success := hq3
        sumSuccess := hsum
        updateSuccess := hupdate }⟩

private theorem finishedBodyExposesIterator
    (prepared : Array RawPrepared 3#usize)
    (state : FoldState) (output : Array RawQM31 256#usize)
    (edge : v6_transcript.fold_values_prefix_loop.body
      prepared state.1 state.2 = ok (done output)) :
    ∃ iterAfter,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
          ok (none, iterAfter) ∧ output = state.2 := by
  rcases state with ⟨iter, values⟩
  unfold v6_transcript.fold_values_prefix_loop.body at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, hiterator, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      exact ⟨iterAfter, hiterator,
        (ControlFlow.done.inj (Result.ok.inj edge)).symm⟩
  | some index =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨offset, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨q, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨offset1, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨q1, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨offset2, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨q2, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨offset3, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨q3, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨q4, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨updated, _, edge⟩ := edge
      cases edge

private theorem rangeNextNoneFinished
    (iter iterAfter : core.ops.range.Range Std.Usize)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      ok (none, iterAfter)) :
    iter.end.val ≤ iter.start.val := by
  by_contra hnot
  have active : iter.start.val < iter.end.val := by omega
  obtain ⟨⟨option, advanced⟩, activeRun, optionEq, _, _⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_Usize_some_spec iter active)
  have outputs := Result.ok.inj (activeRun.symm.trans run)
  have options := congrArg Prod.fst outputs
  simp [optionEq] at options

private theorem stepPreservesInvariant
    (base : Array RawQM31 256#usize)
    (alpha alpha2 alpha3 : RawQM31)
    (prepared : Array RawPrepared 3#usize)
    (state nextState : FoldState)
    (halpha2Exact : generatedQm31ToExact alpha2 = generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 = generatedQm31ToExact alpha ^ 3)
    (hprepared : PreparedArrayFor3 prepared
      (Array.make 3#usize [alpha, alpha2, alpha3]))
    (hend : state.1.end.val ≤ 64)
    (invariant : FoldPrefixInvariant base state.2
      (generatedQm31ToExact alpha) state.1.start.val state.1.end.val)
    (step : ExactFoldStep prepared state nextState) :
    nextState.1.end.val = state.1.end.val ∧
      FoldPrefixInvariant base nextState.2
        (generatedQm31ToExact alpha)
        nextState.1.start.val nextState.1.end.val := by
  obtain ⟨active, indexExact, nextStart, sameEnd⟩ :=
    range_next_some_exact state.1 nextState.1 step.index
      step.iteratorSuccess
  have indexVal : step.index.val = state.1.start.val :=
    congrArg UScalar.val indexExact
  have indexBelow64 : step.index.val < 64 := by omega
  have offsetVal : step.offset.val = 4 * step.index.val := by
    rw [← step.offsetSuccess]
    exact wrappingMulFourExact step.index indexBelow64
  have offset3Bound : step.offset.val + 3 < 256 := by omega
  have offset1Val : step.offset1.val = step.offset.val + 1 := by
    rw [← step.offset1Success]
    apply wrappingAddSmallExact
    norm_num
    omega
  have offset2Val : step.offset2.val = step.offset.val + 2 := by
    rw [← step.offset2Success]
    apply wrappingAddSmallExact
    norm_num
    omega
  have offset3Val : step.offset3.val = step.offset.val + 3 := by
    rw [← step.offset3Success]
    exact wrappingAddSmallExact step.offset 3#usize offset3Bound
  have offsetBound : step.offset.val < 256 := by omega
  have offset1Bound : step.offset1.val < 256 := by omega
  have offset2Bound : step.offset2.val < 256 := by omega
  have offset3Bound' : step.offset3.val < 256 := by omega
  have qEq : step.q = state.2.val[step.offset.val]! :=
    Result.ok.inj (step.qSuccess.symm.trans
      (arrayIndexRun state.2 step.offset offsetBound))
  have q1Eq : step.q1 = state.2.val[step.offset1.val]! :=
    Result.ok.inj (step.q1Success.symm.trans
      (arrayIndexRun state.2 step.offset1 offset1Bound))
  have q2Eq : step.q2 = state.2.val[step.offset2.val]! :=
    Result.ok.inj (step.q2Success.symm.trans
      (arrayIndexRun state.2 step.offset2 offset2Bound))
  have q3Eq : step.q3 = state.2.val[step.offset3.val]! :=
    Result.ok.inj (step.q3Success.symm.trans
      (arrayIndexRun state.2 step.offset3 offset3Bound'))
  have offsetAfterProcessed : state.1.start.val ≤ step.offset.val := by omega
  have offset1AfterProcessed : state.1.start.val ≤ step.offset1.val := by omega
  have offset2AfterProcessed : state.1.start.val ≤ step.offset2.val := by omega
  have offset3AfterProcessed : state.1.start.val ≤ step.offset3.val := by omega
  have qBase : step.q = base.val[4 * step.index.val]! := by
    rw [qEq, invariant.2.2.2.2 _ offsetAfterProcessed offsetBound, offsetVal]
  have q1Base : step.q1 = base.val[4 * step.index.val + 1]! := by
    rw [q1Eq, invariant.2.2.2.2 _ offset1AfterProcessed offset1Bound,
      offset1Val, offsetVal]
  have q2Base : step.q2 = base.val[4 * step.index.val + 2]! := by
    rw [q2Eq, invariant.2.2.2.2 _ offset2AfterProcessed offset2Bound,
      offset2Val, offsetVal]
  have q3Base : step.q3 = base.val[4 * step.index.val + 3]! := by
    rw [q3Eq, invariant.2.2.2.2 _ offset3AfterProcessed offset3Bound',
      offset3Val, offsetVal]
  have rightCanonical : GeneratedCanonicalQM31Array3
      (Array.make 3#usize [step.q1, step.q2, step.q3]) := by
    intro slot hslot
    have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · simpa [Array.make, q1Eq] using invariant.1 step.offset1.val offset1Bound
    · simpa [Array.make, q2Eq] using invariant.1 step.offset2.val offset2Bound
    · simpa [Array.make, q3Eq] using invariant.1 step.offset3.val offset3Bound'
  obtain ⟨q4Expected, q4Run, q4Canonical, q4Exact⟩ :=
    generated_add_sum_products3_prepared_corresponds step.q prepared
      (Array.make 3#usize [alpha, alpha2, alpha3])
      (Array.make 3#usize [step.q1, step.q2, step.q3])
      hprepared rightCanonical
  have q4Eq : step.q4 = q4Expected :=
    Result.ok.inj (step.sumSuccess.symm.trans q4Run)
  subst q4Expected
  have q4FoldExact : generatedQm31ToExact step.q4 =
      coefficientFoldAt base (generatedQm31ToExact alpha) step.index.val := by
    rw [q4Exact]
    simp only [exactProductDot3, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Array.make, List.getElem!_eq_getElem?_getD]
    rw [halpha2Exact, halpha3Exact, qBase, q1Base, q2Base, q3Base]
    unfold coefficientFoldAt exactValueAt
    ring
  have updatedEq : nextState.2 = state.2.set step.index step.q4 :=
    arrayUpdateEqSet state.2 nextState.2 step.index step.q4
      (lt_trans indexBelow64 (by norm_num)) step.updateSuccess
  constructor
  · exact congrArg UScalar.val sameEnd
  · rw [updatedEq]
    refine ⟨canonicalSet state.2 step.index step.q4
      (lt_trans indexBelow64 (by norm_num))
      invariant.1 q4Canonical, ?_, ?_, ?_, ?_⟩
    · rw [nextStart, sameEnd, ← indexVal]
      omega
    · rw [sameEnd]
      exact invariant.2.2.1
    · intro fibre hfibre
      rw [nextStart, ← indexVal] at hfibre
      by_cases hnew : fibre = step.index.val
      · subst fibre
        unfold exactValueAt
        rw [arraySetSame state.2 step.index step.q4
          (lt_trans indexBelow64 (by norm_num))]
        exact q4FoldExact
      · unfold exactValueAt
        rw [arraySetNe state.2 step.index step.q4 fibre hnew]
        exact invariant.2.2.2.1 fibre (by omega)
    · intro other hafter hother
      rw [nextStart, ← indexVal] at hafter
      rw [arraySetNe state.2 step.index step.q4 other (by omega)]
      exact invariant.2.2.2.2 other (by omega) hother

private theorem tracePreservesInvariant
    (base : Array RawQM31 256#usize)
    (alpha alpha2 alpha3 : RawQM31)
    (prepared : Array RawPrepared 3#usize)
    (state : FoldState) (output : Array RawQM31 256#usize)
    (halpha2Exact : generatedQm31ToExact alpha2 = generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 = generatedQm31ToExact alpha ^ 3)
    (hprepared : PreparedArrayFor3 prepared
      (Array.make 3#usize [alpha, alpha2, alpha3]))
    (hend : state.1.end.val ≤ 64)
    (invariant : FoldPrefixInvariant base state.2
      (generatedQm31ToExact alpha) state.1.start.val state.1.end.val)
    (trace : ExactLoopTrace
      (fun state : FoldState =>
        v6_transcript.fold_values_prefix_loop.body prepared state.1 state.2)
      state output) :
    CanonicalValues output ∧
      (∀ fibre, fibre < state.1.end.val →
        exactValueAt output fibre =
          coefficientFoldAt base (generatedQm31ToExact alpha) fibre) ∧
      ∀ index, state.1.end.val ≤ index → index < 256 →
        output.val[index]! = base.val[index]! := by
  cases trace with
  | @done state output edge =>
      obtain ⟨iterAfter, iteratorRun, outputEq⟩ :=
        finishedBodyExposesIterator prepared state output edge
      have finished := rangeNextNoneFinished state.1 iterAfter iteratorRun
      have startLe := invariant.2.1
      have startEq : state.1.start.val = state.1.end.val := by omega
      subst output
      refine ⟨invariant.1, ?_, ?_⟩
      · intro fibre hfibre
        exact invariant.2.2.2.1 fibre (by omega)
      · intro index hindex hbound
        exact invariant.2.2.2.2 index (by omega) hbound
  | @cont state next output edge tail =>
      let step := Classical.choice
        (continuingBodyExposesStep prepared state next edge)
      obtain ⟨sameEnd, nextInvariant⟩ :=
        stepPreservesInvariant base alpha alpha2 alpha3 prepared state next
          halpha2Exact halpha3Exact hprepared hend
          invariant step
      have nextEndBound : next.1.end.val ≤ 64 := by
        rw [sameEnd]
        exact hend
      have result := tracePreservesInvariant base alpha alpha2 alpha3 prepared
        next output halpha2Exact halpha3Exact hprepared
        nextEndBound nextInvariant tail
      simpa [sameEnd] using result
private theorem initialInvariant
    (values : Array RawQM31 256#usize) (alpha : ExactQM31)
    (limit : Nat) (hlimit : limit ≤ 64)
    (hvalues : CanonicalValues values) :
    FoldPrefixInvariant values values alpha 0 limit := by
  refine ⟨hvalues, by omega, hlimit, ?_, ?_⟩
  · intro fibre hfibre
    omega
  · intro index _ _
    rfl

/-- A successful call of the current generated helper computes exactly one
natural coefficient-fold layer into the first `n` array slots and leaves the
remaining storage unchanged. -/
theorem fold_values_prefix_exact
    (input : Std.Usize) (values output : Array RawQM31 256#usize)
    (alpha : RawQM31) (n : Nat)
    (hinput : input.val = 4 * n)
    (hn : n ≤ 64)
    (hvalues : CanonicalValues values)
    (halpha : GeneratedCanonicalQM31 alpha)
    (run : v6_transcript.fold_values_prefix input values alpha = ok output) :
    CanonicalValues output ∧
      (∀ fibre, fibre < n →
        exactValueAt output fibre =
          coefficientFoldAt values (generatedQm31ToExact alpha) fibre) ∧
      ∀ index, n ≤ index → index < 256 →
        output.val[index]! = values.val[index]! := by
  obtain ⟨alpha2, alpha2Run, alpha2Canonical, alpha2Exact⟩ :=
    generated_qm31_square_corresponds alpha halpha
  obtain ⟨alpha3, alpha3Run, alpha3Canonical, alpha3ExactMul⟩ :=
    generated_qm31_mul_corresponds alpha2 alpha alpha2Canonical halpha
  have alpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3 := by
    rw [alpha3ExactMul, alpha2Exact]
    ring
  obtain ⟨p0, p0Run, p0Represents⟩ :=
    generated_prepared_new_establishes alpha halpha
  obtain ⟨p1, p1Run, p1Represents⟩ :=
    generated_prepared_new_establishes alpha2 alpha2Canonical
  obtain ⟨p2, p2Run, p2Represents⟩ :=
    generated_prepared_new_establishes alpha3 alpha3Canonical
  let prepared : Array RawPrepared 3#usize :=
    Array.make 3#usize [p0, p1, p2]
  have preparedFor : PreparedArrayFor3 prepared
      (Array.make 3#usize [alpha, alpha2, alpha3]) := by
    intro index hindex
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · simpa [prepared, Array.make] using
        V7CallerCurrentReleaseR26PreparedSum3Semantics.representsPrepared_implies_preparedFor
          p0 alpha p0Represents halpha
    · simpa [prepared, Array.make] using
        V7CallerCurrentReleaseR26PreparedSum3Semantics.representsPrepared_implies_preparedFor
          p1 alpha2 p1Represents
          alpha2Canonical
    · simpa [prepared, Array.make] using
        V7CallerCurrentReleaseR26PreparedSum3Semantics.representsPrepared_implies_preparedFor
          p2 alpha3 p2Represents
          alpha3Canonical
  obtain ⟨quotient, quotientRun, quotientVal⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Std.Usize.div_spec input (y := 4#usize) (by norm_num))
  have quotientExact : quotient.val = n := by
    have qv : quotient.val = input.val / 4 := by simpa using quotientVal
    rw [qv, hinput]
    omega
  have loopRun : v6_transcript.fold_values_prefix_loop
      { start := 0#usize, «end» := quotient } values prepared = ok output := by
    unfold v6_transcript.fold_values_prefix at run
    rw [alpha2Run] at run
    simp only [bind_tc_ok] at run
    rw [alpha3Run] at run
    simp only [bind_tc_ok] at run
    rw [p0Run] at run
    simp only [bind_tc_ok] at run
    rw [p1Run] at run
    simp only [bind_tc_ok] at run
    rw [p2Run] at run
    simp only [bind_tc_ok] at run
    rw [quotientRun] at run
    simpa only [bind_tc_ok, prepared] using run
  have traceNonempty := loop_success_yields_exact_trace
    (fun state : FoldState =>
      v6_transcript.fold_values_prefix_loop.body prepared state.1 state.2)
    ({ start := 0#usize, «end» := quotient }, values) output (by
      simpa only [v6_transcript.fold_values_prefix_loop] using loopRun)
  let trace := Classical.choice traceNonempty
  have result := tracePreservesInvariant values alpha alpha2 alpha3 prepared
    ({ start := 0#usize, «end» := quotient }, values) output
    alpha2Exact alpha3Exact preparedFor
    (by change quotient.val ≤ 64; rw [quotientExact]; exact hn)
    (initialInvariant values (generatedQm31ToExact alpha)
      quotient.val (by omega) hvalues) trace
  simpa [quotientExact] using result

#print axioms fold_values_prefix_exact

end V7CallerCurrentReleaseR26FoldValuesPrefixSemantics
