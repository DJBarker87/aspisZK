import V7CallerCurrentReleaseR26LineBatchFactorLoop

/-!
# Exact current R26 line-batch accumulation

This file composes the verified inner line-factor loop across the parallel
scale and line-coordinate slices.  The generated loop therefore denotes the
ordered sum of the exact per-line products.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace V7CallerCurrentReleaseR26LineBatchLoop

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26LineBatchFactorLoop

abbrev M31 := V7CallerCurrentReleaseR26.field.M31
abbrev QM31 := V7CallerCurrentReleaseR26.field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

instance : Inhabited M31 := ⟨V7CallerCurrentReleaseR26.field.M31.ZERO⟩
instance : Inhabited QM31 := ⟨V7CallerCurrentReleaseR26.field.QM31.ZERO⟩

def CanonicalQM31Slice (values : Slice QM31) : Prop :=
  ∀ i, i < values.length → GeneratedCanonicalQM31 values.val[i]!

def CanonicalM31Slice (values : Slice M31) : Prop :=
  ∀ i, i < values.length → GeneratedCanonicalM31 values.val[i]!

def lineBatchTerm (logLen : Std.U32) (scales : Slice QM31)
    (xs : Slice M31) (index : Std.U32) (position : Nat) : ExactQM31 :=
  linePrefix scales.val[position]! xs.val[position]! index logLen.val

def lineBatchPrefix (logLen : Std.U32) (scales : Slice QM31)
    (xs : Slice M31) (index : Std.U32) (processed : Nat) : ExactQM31 :=
  ∑ position ∈ Finset.range processed,
    lineBatchTerm logLen scales xs index position

def LineBatchInvariant (logLen : Std.U32) (scales : Slice QM31)
    (xs : Slice M31) (index : Std.U32) (sum : QM31)
    (processed : Nat) : Prop :=
  GeneratedCanonicalQM31 sum ∧
    generatedQm31ToExact sum =
      lineBatchPrefix logLen scales xs index processed

private theorem slice_index_run
    {T : Type} [Inhabited T] (values : Slice T) (position : Std.Usize)
    (active : position.val < values.length) :
    Slice.index_usize values position = ok values.val[position.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.index_usize_spec values position (by simpa using active))
  have listExact : values.val[position.val] = values.val[position.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using active
  simpa [exact, listExact] using run

private theorem body_done
    (logLen : Std.U32) (scales : Slice QM31) (xs : Slice M31)
    (index : Std.U32) (sum : QM31) (position : Std.Usize)
    (done : ¬ position.val < scales.length) :
    V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0.body
        logLen scales xs index sum position = ok (ControlFlow.done sum) := by
  unfold V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0.body
  rw [if_neg]
  simpa using done

private theorem body_active
    (logLen : Std.U32) (scales : Slice QM31) (xs : Slice M31)
    (index : Std.U32) (sum : QM31) (position : Std.Usize)
    (logBound : logLen.val ≤ 32)
    (sameLength : scales.length = xs.length)
    (scalesCanonical : CanonicalQM31Slice scales)
    (xsCanonical : CanonicalM31Slice xs)
    (active : position.val < scales.length)
    (invariant : LineBatchInvariant logLen scales xs index sum position.val) :
    ∃ nextSum nextPosition,
      V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0.body
          logLen scales xs index sum position =
        ok (ControlFlow.cont (nextSum, nextPosition)) ∧
      nextPosition.val = position.val + 1 ∧
      LineBatchInvariant logLen scales xs index nextSum nextPosition.val := by
  have xsActive : position.val < xs.length := by simpa [sameLength] using active
  have scaleRead := slice_index_run scales position active
  have xRead := slice_index_run xs position xsActive
  let scale := scales.val[position.val]!
  let x := xs.val[position.val]!
  have scaleCanonical : GeneratedCanonicalQM31 scale :=
    scalesCanonical position.val active
  have xCanonical : GeneratedCanonicalM31 x :=
    xsCanonical position.val xsActive
  obtain ⟨lineValue, lineRun, lineCanonical, lineExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (generated_line_factor_loop_corresponds logLen index scale x logBound
        scaleCanonical xCanonical)
  obtain ⟨nextSum, addRun, nextCanonical, nextExact⟩ :=
    generated_qm31_add_corresponds sum lineValue invariant.1 lineCanonical
  let nextPosition := Std.Usize.wrapping_add position 1#usize
  have positionBound : position.val + 1 < Usize.size := by
    have sliceBound := scales.property
    have activeList : position.val < scales.val.length := by simpa using active
    simp only [Usize.max, Usize.size, Usize.numBits] at sliceBound ⊢
    omega
  have nextVal : nextPosition.val = position.val + 1 := by
    dsimp only [nextPosition]
    rw [Std.Usize.wrapping_add_val_eq]
    norm_num
    exact Nat.mod_eq_of_lt positionBound
  refine ⟨nextSum, nextPosition, ?_, nextVal, nextCanonical, ?_⟩
  · unfold V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0.body
    rw [if_pos (by simpa using active), if_pos (by simpa using xsActive)]
    rw [scaleRead]
    simp only [bind_tc_ok]
    rw [xRead]
    simp only [bind_tc_ok]
    change
      (V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0_loop0
          logLen index scale x 0#u32 >>= _) = _
    rw [lineRun]
    simp only [bind_tc_ok]
    rw [addRun]
    simp only [bind_tc_ok, Std.lift]
    rfl
  · rw [nextExact, invariant.2, lineExact, nextVal]
    simp [lineBatchPrefix, lineBatchTerm, Finset.sum_range_succ, scale, x]

/-- The generated outer line-batch loop returns the exact sum of its aligned
scale/coordinate entries. -/
theorem generated_line_batch_loop_corresponds
    (logLen : Std.U32) (scales : Slice QM31) (xs : Slice M31)
    (index : Std.U32)
    (logBound : logLen.val ≤ 32)
    (sameLength : scales.length = xs.length)
    (scalesCanonical : CanonicalQM31Slice scales)
    (xsCanonical : CanonicalM31Slice xs) :
    V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0
        logLen scales xs index V7CallerCurrentReleaseR26.field.QM31.ZERO 0#usize
      ⦃ out => GeneratedCanonicalQM31 out ∧
        generatedQm31ToExact out =
          lineBatchPrefix logLen scales xs index scales.length ⦄ := by
  simp only [V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed_loop0]
  apply loop.spec_decr_nat
    (fun state : QM31 × Std.Usize => scales.length - state.2.val)
    (fun state => state.2.val ≤ scales.length ∧
      LineBatchInvariant logLen scales xs index state.1 state.2.val)
    (fun out => GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        lineBatchPrefix logLen scales xs index scales.length)
  · rintro ⟨sum, position⟩ ⟨positionLe, stateInvariant⟩
    dsimp only at positionLe stateInvariant ⊢
    by_cases active : position.val < scales.length
    · obtain ⟨nextSum, nextPosition, bodyRun, nextVal, nextInvariant⟩ :=
        body_active logLen scales xs index sum position logBound sameLength
          scalesCanonical xsCanonical active stateInvariant
      rw [bodyRun]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, nextInvariant⟩, ?_⟩ <;> rw [nextVal] <;> omega
    · have atEnd : position.val = scales.length := by omega
      rw [body_done logLen scales xs index sum position active]
      simpa [atEnd, LineBatchInvariant] using stateInvariant
  · refine ⟨by norm_num, ?_, ?_⟩
    · norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
        AspisAeneasCM31Multiplicative.CanonicalRawM31,
        V7CallerCurrentReleaseR26.field.QM31.ZERO]
    · apply QuadraticAlgebra.ext
      · apply QuadraticAlgebra.ext <;>
          simp [lineBatchPrefix, generatedQm31ToExact, generatedCm31ToExact,
            V7CallerCurrentReleaseR26.field.QM31.ZERO]
      · apply QuadraticAlgebra.ext <;>
          simp [lineBatchPrefix, generatedQm31ToExact, generatedCm31ToExact,
            V7CallerCurrentReleaseR26.field.QM31.ZERO]

#print axioms generated_line_batch_loop_corresponds

private theorem halve_qm31_zero (value : QM31) :
    V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.halve_qm31
        value 0#u8 = ok value := by
  simp [V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.halve_qm31,
    V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.halve_qm31_loop,
    V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.halve_qm31_loop.body,
    loop, UScalar.lt_equiv]

/-- A line batch appended by the query path has zero deferred halvings, so its
public generated evaluator has the same exact sum as the outer loop. -/
theorem generated_line_batch_zero_deferred_corresponds
    (logLen : Std.U32) (scales : Slice QM31) (xs : Slice M31)
    (index : Std.U32)
    (logBound : logLen.val ≤ 32)
    (sameLength : scales.length = xs.length)
    (scalesCanonical : CanonicalQM31Slice scales)
    (xsCanonical : CanonicalM31Slice xs) :
    V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed
        logLen scales xs 0#u8 index
      ⦃ out => GeneratedCanonicalQM31 out ∧
        generatedQm31ToExact out =
          lineBatchPrefix logLen scales xs index scales.length ⦄ := by
  unfold V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed
  obtain ⟨sum, sumRun, sumCanonical, sumExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (generated_line_batch_loop_corresponds logLen scales xs index logBound
        sameLength scalesCanonical xsCanonical)
  rw [sumRun]
  simp only [bind_tc_ok]
  rw [halve_qm31_zero]
  simp [sumCanonical, sumExact]

#print axioms generated_line_batch_zero_deferred_corresponds

end V7CallerCurrentReleaseR26LineBatchLoop
