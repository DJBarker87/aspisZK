import V7CallerCurrentReleaseR26TerminalLineStep

/-!
# Complete sixteen-line optimized terminal batch

The generated batch loop is lifted through the verified one-line transition.
Its postcondition exposes the four constant coefficients and the twelve line
coefficients as symbolic sums over the sixteen source entries.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow
open scoped BigOperators
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineBatch

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26LineBatchFoldLoop
open V7CallerCurrentReleaseR26TerminalLineAccumulator
open V7CallerCurrentReleaseR26TerminalLineRawLoop
open V7CallerCurrentReleaseR26TerminalLineLimbLoop
open V7CallerCurrentReleaseR26TerminalLineFlushLimb
open V7CallerCurrentReleaseR26TerminalLineStep

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def terminalScaleAt (values : Slice RawQM31) (index : Nat) : RawQM31 :=
  values.val[index]!

def terminalXAt (values : Slice RawM31) (index : Nat) : RawM31 :=
  values.val[index]!

def TerminalCanonicalQM31Slice (values : Slice RawQM31) : Prop :=
  ∀ index, index < values.val.length →
    GeneratedCanonicalQM31 (terminalScaleAt values index)

def TerminalCanonicalM31Slice (values : Slice RawM31) : Prop :=
  ∀ index, index < values.val.length →
    GeneratedCanonicalM31 (terminalXAt values index)

def terminalConstantPrefix (scales : Slice RawQM31)
    (processed limb : Nat) : ExactM31 :=
  ∑ position ∈ Finset.range processed,
    exactScaleLimb (terminalScaleAt scales position) limb

def terminalLinePrefix (scales : Slice RawQM31) (xs : Slice RawM31)
    (processed slot limb : Nat) : ExactM31 :=
  ∑ position ∈ Finset.range processed,
    exactScaleLimb (terminalScaleAt scales position) limb *
      exactLineFactor (terminalXAt xs position) slot

def TerminalBatchInvariant
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (baseConstant : Array RawM31 4#usize)
    (baseRaw : Array (Array Std.U64 4#usize) 3#usize)
    (baseSums : Array (Array RawM31 4#usize) 3#usize)
    (count : Std.Usize) (constant : Array RawM31 4#usize)
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (sums : Array (Array RawM31 4#usize) 3#usize)
    (batchIndex : Std.Usize) : Prop :=
  count.val = batchIndex.val ∧
  batchIndex.val ≤ 16 ∧
  LineAccumulatorStateInvariant batchIndex.val constant raw sums ∧
  (∀ limb, limb < 4 →
    generatedM31ToExact (constantCell constant limb) =
      generatedM31ToExact (constantCell baseConstant limb) +
        terminalConstantPrefix scales batchIndex.val limb) ∧
  (∀ slot, slot < 3 → ∀ limb, limb < 4 →
    generatedM31ToExact (sumCell sums slot limb) +
        ((rawCell raw slot limb).val : ExactM31) =
      generatedM31ToExact (sumCell baseSums slot limb) +
        ((rawCell baseRaw slot limb).val : ExactM31) +
        terminalLinePrefix scales xs batchIndex.val slot limb)

private theorem sliceIndexRun
    {T : Type} [Inhabited T] (values : Slice T) (index : Std.Usize)
    (active : index.val < values.val.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.index_usize_spec values index active)
  have listExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simp [active]
  simpa [exact, listExact] using run

private theorem wrappingSuccVal
    (index : Std.Usize) (bound : index.val < 16) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  apply Nat.mod_eq_of_lt
  have small : index.val + 1 < 17 := by omega
  apply lt_trans small
  rw [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num

private theorem batchBodyActive
    (deferred : Std.U8) (scales : Slice RawQM31) (xs : Slice RawM31)
    (baseConstant : Array RawM31 4#usize)
    (baseRaw : Array (Array Std.U64 4#usize) 3#usize)
    (baseSums : Array (Array RawM31 4#usize) 3#usize)
    (count : Std.Usize) (constant : Array RawM31 4#usize)
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (sums : Array (Array RawM31 4#usize) 3#usize)
    (batchIndex : Std.Usize)
    (scalesLength : scales.val.length = 16)
    (xsLength : xs.val.length = 16)
    (scalesCanonical : TerminalCanonicalQM31Slice scales)
    (xsCanonical : TerminalCanonicalM31Slice xs)
    (active : batchIndex.val < 16)
    (invariant : TerminalBatchInvariant scales xs baseConstant baseRaw
      baseSums count constant raw sums batchIndex) :
    ∃ nextCount nextConstant nextRaw nextSums nextIndex,
      sumcheck.WeightAccumulator.impl.accumulate_line_batch_dot_loop.body
          deferred scales xs deferred count constant raw sums batchIndex =
        ok (cont (nextCount, nextConstant, nextRaw, nextSums, nextIndex)) ∧
      nextIndex.val = batchIndex.val + 1 ∧
      TerminalBatchInvariant scales xs baseConstant baseRaw baseSums
        nextCount nextConstant nextRaw nextSums nextIndex := by
  have scaleActive : batchIndex.val < scales.val.length := by omega
  have xActive : batchIndex.val < xs.val.length := by omega
  have scaleRead := sliceIndexRun scales batchIndex scaleActive
  have xRead := sliceIndexRun xs batchIndex xActive
  let scale := terminalScaleAt scales batchIndex.val
  let x := terminalXAt xs batchIndex.val
  have scaleCanonical : GeneratedCanonicalQM31 scale :=
    scalesCanonical batchIndex.val scaleActive
  have xCanonical : GeneratedCanonicalM31 x :=
    xsCanonical batchIndex.val xActive
  have stepSpec := generated_accumulate_line_dot_corresponds batchIndex.val
    active deferred scale x count constant raw sums invariant.1
      scaleCanonical xCanonical invariant.2.2.1
  obtain ⟨stepOut, stepRun, nextCountVal, nextState,
      constantDelta, lineDelta⟩ := Aeneas.Std.WP.spec_imp_exists stepSpec
  let nextCount := stepOut.1
  let nextConstant := stepOut.2.1
  let nextRaw := stepOut.2.2.1
  let nextSums := stepOut.2.2.2
  let nextIndex := Std.Usize.wrapping_add batchIndex 1#usize
  have nextIndexVal : nextIndex.val = batchIndex.val + 1 :=
    wrappingSuccVal batchIndex active
  have bodyRun :
      sumcheck.WeightAccumulator.impl.accumulate_line_batch_dot_loop.body
          deferred scales xs deferred count constant raw sums batchIndex =
        ok (cont (nextCount, nextConstant, nextRaw, nextSums, nextIndex)) := by
    unfold sumcheck.WeightAccumulator.impl.accumulate_line_batch_dot_loop.body
    simp only [Slice.len_val]
    rw [if_pos (by simpa [scalesLength] using active)]
    rw [if_pos (by simpa [xsLength] using active)]
    rw [scaleRead]
    simp only [bind_tc_ok]
    rw [xRead]
    simp only [bind_tc_ok]
    have stepRun' :
        sumcheck.WeightAccumulator.impl.accumulate_line_dot deferred
            scales.val[batchIndex.val]! xs.val[batchIndex.val]!
            deferred count constant raw sums = ok stepOut := by
      simpa [scale, x, terminalScaleAt, terminalXAt] using stepRun
    rw [stepRun']
    simp only [bind_tc_ok, Std.lift]
    simp [nextCount, nextConstant, nextRaw, nextSums, nextIndex]
  refine ⟨nextCount, nextConstant, nextRaw, nextSums, nextIndex,
    bodyRun, nextIndexVal, ?_⟩
  unfold TerminalBatchInvariant
  constructor
  · rw [nextCountVal, nextIndexVal]
  constructor
  · rw [nextIndexVal]
    omega
  constructor
  · rw [nextIndexVal]
    exact nextState
  constructor
  · intro limb limbBound
    rw [constantDelta limb limbBound]
    rw [invariant.2.2.2.1 limb limbBound]
    rw [nextIndexVal]
    simp [terminalConstantPrefix, Finset.sum_range_succ, scale,
      terminalScaleAt]
    ring
  · intro slot slotBound limb limbBound
    rw [lineDelta slot slotBound limb limbBound]
    rw [invariant.2.2.2.2 slot slotBound limb limbBound]
    rw [nextIndexVal]
    simp [terminalLinePrefix, Finset.sum_range_succ, scale, x,
      terminalScaleAt, terminalXAt]
    ring

theorem generated_terminal_line_batch_loop_corresponds
    (deferred : Std.U8) (scales : Slice RawQM31) (xs : Slice RawM31)
    (baseConstant : Array RawM31 4#usize)
    (baseRaw : Array (Array Std.U64 4#usize) 3#usize)
    (baseSums : Array (Array RawM31 4#usize) 3#usize)
    (scalesLength : scales.val.length = 16)
    (xsLength : xs.val.length = 16)
    (scalesCanonical : TerminalCanonicalQM31Slice scales)
    (xsCanonical : TerminalCanonicalM31Slice xs)
    (baseState : LineAccumulatorStateInvariant 0
      baseConstant baseRaw baseSums) :
    sumcheck.WeightAccumulator.impl.accumulate_line_batch_dot_loop
        deferred scales xs deferred 0#usize baseConstant baseRaw baseSums 0#usize
      ⦃ out =>
        out.1.val = 16 ∧
        LineAccumulatorStateInvariant 16 out.2.1 out.2.2.1 out.2.2.2 ∧
        (∀ limb, limb < 4 →
          generatedM31ToExact (constantCell out.2.1 limb) =
            generatedM31ToExact (constantCell baseConstant limb) +
              terminalConstantPrefix scales 16 limb) ∧
        (∀ slot, slot < 3 → ∀ limb, limb < 4 →
          generatedM31ToExact (sumCell out.2.2.2 slot limb) +
              ((rawCell out.2.2.1 slot limb).val : ExactM31) =
            generatedM31ToExact (sumCell baseSums slot limb) +
              ((rawCell baseRaw slot limb).val : ExactM31) +
              terminalLinePrefix scales xs 16 slot limb) ⦄ := by
  simp only [sumcheck.WeightAccumulator.impl.accumulate_line_batch_dot_loop]
  apply loop.spec_decr_nat
    (fun state : Std.Usize × Array RawM31 4#usize ×
      Array (Array Std.U64 4#usize) 3#usize ×
      Array (Array RawM31 4#usize) 3#usize × Std.Usize =>
        16 - state.2.2.2.2.val)
    (fun state => TerminalBatchInvariant scales xs baseConstant baseRaw
      baseSums state.1 state.2.1 state.2.2.1 state.2.2.2.1
        state.2.2.2.2)
    (fun out : Std.Usize × Array RawM31 4#usize ×
        Array (Array Std.U64 4#usize) 3#usize ×
        Array (Array RawM31 4#usize) 3#usize =>
      out.1.val = 16 ∧
      LineAccumulatorStateInvariant 16 out.2.1 out.2.2.1 out.2.2.2 ∧
      (∀ limb, limb < 4 →
        generatedM31ToExact (constantCell out.2.1 limb) =
          generatedM31ToExact (constantCell baseConstant limb) +
            terminalConstantPrefix scales 16 limb) ∧
      (∀ slot, slot < 3 → ∀ limb, limb < 4 →
        generatedM31ToExact (sumCell out.2.2.2 slot limb) +
            ((rawCell out.2.2.1 slot limb).val : ExactM31) =
          generatedM31ToExact (sumCell baseSums slot limb) +
            ((rawCell baseRaw slot limb).val : ExactM31) +
            terminalLinePrefix scales xs 16 slot limb))
  · rintro ⟨count, constant, raw, sums, batchIndex⟩ invariant
    dsimp only at invariant ⊢
    by_cases active : batchIndex.val < 16
    · obtain ⟨nextCount, nextConstant, nextRaw, nextSums, nextIndex,
          bodyRun, nextIndexVal, nextInvariant⟩ :=
        batchBodyActive deferred scales xs baseConstant baseRaw baseSums
          count constant raw sums batchIndex scalesLength xsLength
          scalesCanonical xsCanonical active invariant
      rw [bodyRun]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨nextInvariant, ?_⟩
      rw [nextIndexVal]
      omega
    · have atEnd : batchIndex.val = 16 := by
        have bound := invariant.2.1
        omega
      unfold sumcheck.WeightAccumulator.impl.accumulate_line_batch_dot_loop.body
      simp only [Slice.len_val]
      rw [if_neg (by simpa [scalesLength] using active)]
      simp only [Aeneas.Std.WP.spec_ok]
      have state := invariant.2.2.1
      have constantExact := invariant.2.2.2.1
      have lineExact := invariant.2.2.2.2
      have countExact := invariant.1
      rw [atEnd] at state constantExact lineExact countExact
      exact ⟨countExact, state, constantExact, lineExact⟩
  · refine ⟨rfl, by norm_num, baseState, ?_, ?_⟩
    · intro limb limbBound
      simp [terminalConstantPrefix]
    · intro slot slotBound limb limbBound
      simp [terminalLinePrefix]

#print axioms generated_terminal_line_batch_loop_corresponds

end V7CallerCurrentReleaseR26TerminalLineBatch
