import V7ProductionCallbacksR30Qm31Canonical
import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Canonicality of packed base-field decoder outputs

The production opening decoder masks each packed limb to 31 bits and scans
every recovered word before accepting it.  This module follows those literal
generated loops symbolically; it never normalizes a packed byte sequence.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30DecoderCanonical

open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26FieldBridge

abbrev RawM31 := V7ProductionCallbacksR29.aspis_core.field.M31
abbrev ScanIter := core.slice.iter.Iter Std.U32
abbrev ScanState := ScanIter × Std.U32

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

def ScannerCanonical (iter : ScanIter) : Prop :=
  ∀ index, iter.i ≤ index → index < iter.slice.length →
    AspisAeneasCM31Multiplicative.CanonicalRawM31 iter.slice.val[index]!

private def scanBody (state : ScanState) :
    Result (ControlFlow ScanState Std.U32) :=
  V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0_loop0.body
    state.1 state.2

private theorem scan_body_done_canonical
    (state : ScanState) (invalid : Std.U32)
    (edge : scanBody state = ok (done invalid)) :
    ScannerCanonical state.1 := by
  rcases state with ⟨iter, prior⟩
  unfold scanBody at edge
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0_loop0.body
    at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      intro index lower upper
      change iter.i ≤ index at lower
      change index < iter.slice.length at upper
      change core.slice.iter.IteratorSliceIter.next iter =
        ok (none, iterAfter) at iteratorRun
      unfold core.slice.iter.IteratorSliceIter.next at iteratorRun
      split at iteratorRun
      · simp at iteratorRun
      · have hlength : (iter.slice.len).val = iter.slice.length := by rfl
        omega
  | some value =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨indicator, indicatorRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨invalidAfter, invalidRun, edge⟩ := edge
      cases edge

structure ScanContinuation (state next : ScanState) : Type where
  value : Std.U32
  iterAfter : ScanIter
  indicator : Std.U32
  iteratorSuccess : core.slice.iter.IteratorSliceIter.next state.1 =
    ok (some value, iterAfter)
  indicatorSuccess : lift (core.convert.num.FromU32Bool.from
    (value >= V7ProductionCallbacksR29.aspis_core.field.P)) = ok indicator
  invalidSuccess : lift (state.2 ||| indicator) = ok next.2
  iteratorExact : next.1 = iterAfter

private theorem scan_body_continuation_exposes
    (state next : ScanState)
    (edge : scanBody state = ok (cont next)) :
    Nonempty (ScanContinuation state next) := by
  rcases state with ⟨iter, prior⟩
  rcases next with ⟨iterNext, invalidNext⟩
  unfold scanBody at edge
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0_loop0.body
    at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none =>
      have impossible : (done prior : ControlFlow ScanState Std.U32) =
          cont (iterNext, invalidNext) :=
        Result.ok.inj edge
      cases impossible
  | some value =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨indicator, indicatorRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨invalidAfter, invalidRun, edge⟩ := edge
      have stateExact : (iterAfter, invalidAfter) = (iterNext, invalidNext) :=
        ControlFlow.cont.inj (Result.ok.inj edge)
      cases stateExact
      exact ⟨{
        value := value
        iterAfter := iterNext
        indicator := indicator
        iteratorSuccess := iteratorRun
        indicatorSuccess := indicatorRun
        invalidSuccess := invalidRun
        iteratorExact := rfl
      }⟩

private theorem continuation_zero_implies_value_canonical
    {state next : ScanState}
    (continuation : ScanContinuation state next)
    (nextZero : next.2 = 0#u32) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31 continuation.value := by
  have hor : state.2 ||| continuation.indicator = next.2 := by
    simpa using Result.ok.inj continuation.invalidSuccess
  have horVal : state.2.val ||| continuation.indicator.val = 0 := by
    have := congrArg UScalar.val hor
    rw [nextZero] at this
    simpa [UScalar.val_or] using this
  have indicatorVal : continuation.indicator.val = 0 := by
    have bound := Nat.right_le_or (n := state.2.val)
      (m := continuation.indicator.val)
    omega
  have indicatorZero : continuation.indicator = 0#u32 := by
    apply UScalar.eq_of_val_eq
    simpa using indicatorVal
  have comparisonFalse :
      decide (continuation.value ≥ V7ProductionCallbacksR29.aspis_core.field.P) =
        false := by
    by_contra comparisonTrue
    have comparisonBool := Bool.eq_true_of_not_eq_false comparisonTrue
    have comparisonProp : continuation.value ≥
        V7ProductionCallbacksR29.aspis_core.field.P := of_decide_eq_true comparisonBool
    have indicatorOne : continuation.indicator = 1#u32 := by
      have indicatorExact := Result.ok.inj continuation.indicatorSuccess
      simpa [core.convert.num.FromU32Bool.from, comparisonBool, comparisonProp] using
        indicatorExact.symm
    rw [indicatorZero] at indicatorOne
    norm_num at indicatorOne
  have valueLtP : continuation.value.val <
      V7ProductionCallbacksR29.aspis_core.field.P.val := by
    simpa using (show ¬ continuation.value ≥
      V7ProductionCallbacksR29.aspis_core.field.P from by
        simpa using comparisonFalse)
  unfold AspisAeneasCM31Multiplicative.CanonicalRawM31
  have callbackP : V7ProductionCallbacksR29.aspis_core.field.P.val = 2147483647 := by
    rw [V7ProductionCallbacksR30FieldCanonical.p_eq]
    exact V7ProductionCallbacksR30FieldCanonical.current_p_val_eq
  simpa [AspisAeneasCM31Multiplicative.m31Modulus, callbackP] using valueLtP

private theorem continuation_zero_implies_prior_zero
    {state next : ScanState}
    (continuation : ScanContinuation state next)
    (nextZero : next.2 = 0#u32) : state.2 = 0#u32 := by
  have hor : state.2 ||| continuation.indicator = next.2 := by
    simpa using Result.ok.inj continuation.invalidSuccess
  have horVal : state.2.val ||| continuation.indicator.val = 0 := by
    have := congrArg UScalar.val hor
    rw [nextZero] at this
    simpa [UScalar.val_or] using this
  apply UScalar.eq_of_val_eq
  have bound := Nat.left_le_or (n := state.2.val)
    (m := continuation.indicator.val)
  change state.2.val = 0
  omega

private theorem scan_body_done_invalid
    (state : ScanState) (invalid : Std.U32)
    (edge : scanBody state = ok (done invalid)) : state.2 = invalid := by
  unfold scanBody at edge
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0_loop0.body
    at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨⟨option, iterAfter⟩, iteratorRun, edge⟩ := edge
  cases option with
  | none => exact ControlFlow.done.inj (Result.ok.inj edge)
  | some value =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨indicator, _, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨invalidAfter, _, edge⟩ := edge
      cases edge

private theorem continuation_canonical_step
    {state next : ScanState}
    (continuation : ScanContinuation state next)
    (valueCanonical : AspisAeneasCM31Multiplicative.CanonicalRawM31 continuation.value)
    (tailCanonical : ScannerCanonical next.1) : ScannerCanonical state.1 := by
  have iteratorRun := continuation.iteratorSuccess
  unfold core.slice.iter.IteratorSliceIter.next at iteratorRun
  split at iteratorRun
  · have exactPair := Result.ok.inj iteratorRun
    have valueExact := Option.some.inj (congrArg Prod.fst exactPair)
    have iteratorExact := congrArg Prod.snd exactPair
    have nextExact : next.1 = { state.1 with i := state.1.i + 1 } :=
      continuation.iteratorExact.trans iteratorExact.symm
    intro index lower upper
    by_cases current : index = state.1.i
    · subst index
      have indexBound : state.1.i < state.1.slice.val.length := by
        simpa only using upper
      have valueAt : continuation.value = state.1.slice.val[state.1.i]! := by
        rw [← List.Inhabited_getElem_eq_getElem! state.1.slice.val state.1.i indexBound]
        exact valueExact.symm
      exact valueAt ▸ valueCanonical
    · have nextLower : next.1.i ≤ index := by rw [nextExact]; dsimp; omega
      have nextUpper : index < next.1.slice.length := by simpa [nextExact] using upper
      have result := tailCanonical index nextLower nextUpper
      simpa [nextExact] using result
  · simp at iteratorRun

/-- A zero final invalid flag certifies every remaining word of the literal
scanner, and also forces its initial flag to be zero. -/
theorem scanner_trace_zero_canonical
    {state : ScanState} {invalid : Std.U32}
    (trace : ExactLoopTrace scanBody state invalid) :
    invalid = 0#u32 → state.2 = 0#u32 ∧ ScannerCanonical state.1 := by
  induction trace with
  | done edge =>
      intro zero
      exact ⟨(scan_body_done_invalid _ _ edge).trans zero,
        scan_body_done_canonical _ _ edge⟩
  | cont edge tail ih =>
      intro zero
      obtain ⟨continuation⟩ := scan_body_continuation_exposes _ _ edge
      obtain ⟨nextZero, nextCanonical⟩ := ih zero
      exact ⟨continuation_zero_implies_prior_zero continuation nextZero,
        continuation_canonical_step continuation
          (continuation_zero_implies_value_canonical continuation nextZero)
          nextCanonical⟩

theorem successful_scanner_zero_canonical
    (iter : ScanIter) (prior : Std.U32)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0_loop0
      iter prior = ok 0#u32) :
    prior = 0#u32 ∧ ScannerCanonical iter := by
  have loopRun : loop scanBody (iter, prior) = ok 0#u32 := run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace scanBody (iter, prior) 0#u32 loopRun
  exact scanner_trace_zero_canonical trace rfl

#print axioms successful_scanner_zero_canonical

end V7ProductionCallbacksR30DecoderCanonical
