import V7CallerCurrentReleaseR26TerminalLineLimbLoop

/-!
# Per-slot flush for the terminal line accumulator

The generated flush reduces four U64 raw cells into canonical M31 sums and
sets those raw cells to zero.  This is the inner loop used after every fourth
line.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineFlushLimb

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26TerminalLineRawLoop

abbrev RawM31 := field.M31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩

def sumCell
    (sums : Array (Array RawM31 4#usize) 3#usize)
    (slot limb : Nat) : RawM31 :=
  sums.val[slot]!.val[limb]!

def CanonicalLineSums
    (sums : Array (Array RawM31 4#usize) 3#usize) : Prop :=
  ∀ slot, slot < 3 → ∀ limb, limb < 4 →
    GeneratedCanonicalM31 (sumCell sums slot limb)

def flushRawCell
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (slot limb : Std.Usize) : Array (Array Std.U64 4#usize) 3#usize :=
  raw.set slot ((raw.val[slot.val]!).set limb 0#u64)

def flushSumCell
    (sums : Array (Array RawM31 4#usize) 3#usize)
    (slot limb : Std.Usize) (value : RawM31) :
    Array (Array RawM31 4#usize) 3#usize :=
  sums.set slot ((sums.val[slot.val]!).set limb value)

def FlushLimbInvariant
    (baseRaw currentRaw : Array (Array Std.U64 4#usize) 3#usize)
    (baseSums currentSums : Array (Array RawM31 4#usize) 3#usize)
    (slot processed : Nat) : Prop :=
  CanonicalLineSums currentSums ∧
  (∀ row, row < 3 → ∀ limb, limb < 4 →
    (rawCell currentRaw row limb).val =
      if row = slot ∧ limb < processed then 0
      else (rawCell baseRaw row limb).val) ∧
  (∀ row, row < 3 → ∀ limb, limb < 4 →
    generatedM31ToExact (sumCell currentSums row limb) =
      if row = slot ∧ limb < processed then
        generatedM31ToExact (sumCell baseSums row limb) +
          ((rawCell baseRaw row limb).val : ExactM31)
      else generatedM31ToExact (sumCell baseSums row limb))

private theorem arrayIndexRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hbang : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    simp
  simpa [valueEq, hbang] using run

private theorem arrayIndexMutRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_mut_usize values index =
      ok (values.val[index.val]!, values.set index) := by
  obtain ⟨result, run, post⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_mut_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  rcases result with ⟨value, back⟩
  rcases post with ⟨valueEq, backEq⟩
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hbang : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    simp
  simpa [valueEq, backEq, hbang] using run

private theorem arrayUpdateRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (hindex : index.val < N.val) :
    Array.update values index value = ok (values.set index value) := by
  obtain ⟨out, run, outEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value (by
      simpa [Array.length_eq] using hindex))
  simpa [outEq] using run

private theorem rawCellFlushSame
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (slot limb : Std.Usize) (slotBound : slot.val < 3)
    (limbBound : limb.val < 4) :
    rawCell (flushRawCell raw slot limb) slot.val limb.val = 0#u64 := by
  unfold rawCell flushRawCell
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using slotBound, rfl⟩)]
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using limbBound, rfl⟩)]

private theorem rawCellFlushFrame
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (slot limb : Std.Usize) (row column : Nat)
    (rowBound : row < 3) (_columnBound : column < 4)
    (different : row ≠ slot.val ∨ column ≠ limb.val) :
    rawCell (flushRawCell raw slot limb) row column = rawCell raw row column := by
  unfold rawCell flushRawCell
  simp only [Array.set_val_eq]
  by_cases sameRow : row = slot.val
  · subst row
    rw [List.set_getElem!_eq _ _ _ _ (by
      exact ⟨by simpa [Array.length_eq] using rowBound, rfl⟩)]
    simp only [Array.set_val_eq]
    rw [List.set_getElem!_ne _ _ _ _ (by omega)]
  · rw [List.set_getElem!_ne _ _ _ _ (by omega)]

private theorem sumCellFlushSame
    (sums : Array (Array RawM31 4#usize) 3#usize)
    (slot limb : Std.Usize) (value : RawM31)
    (slotBound : slot.val < 3) (limbBound : limb.val < 4) :
    sumCell (flushSumCell sums slot limb value) slot.val limb.val = value := by
  unfold sumCell flushSumCell
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using slotBound, rfl⟩)]
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using limbBound, rfl⟩)]

private theorem sumCellFlushFrame
    (sums : Array (Array RawM31 4#usize) 3#usize)
    (slot limb : Std.Usize) (value : RawM31) (row column : Nat)
    (rowBound : row < 3) (_columnBound : column < 4)
    (different : row ≠ slot.val ∨ column ≠ limb.val) :
    sumCell (flushSumCell sums slot limb value) row column =
      sumCell sums row column := by
  unfold sumCell flushSumCell
  simp only [Array.set_val_eq]
  by_cases sameRow : row = slot.val
  · subst row
    rw [List.set_getElem!_eq _ _ _ _ (by
      exact ⟨by simpa [Array.length_eq] using rowBound, rfl⟩)]
    simp only [Array.set_val_eq]
    rw [List.set_getElem!_ne _ _ _ _ (by omega)]
  · rw [List.set_getElem!_ne _ _ _ _ (by omega)]

private theorem flushLimbInvariantStep
    (baseRaw currentRaw : Array (Array Std.U64 4#usize) 3#usize)
    (baseSums currentSums : Array (Array RawM31 4#usize) 3#usize)
    (slot limb : Std.Usize) (slotBound : slot.val < 3)
    (limbBound : limb.val < 4) (nextSum : RawM31)
    (nextSumCanonical : GeneratedCanonicalM31 nextSum)
    (nextSumExact : generatedM31ToExact nextSum =
      generatedM31ToExact (sumCell currentSums slot.val limb.val) +
        ((rawCell currentRaw slot.val limb.val).val : ExactM31))
    (invariant : FlushLimbInvariant baseRaw currentRaw baseSums currentSums
      slot.val limb.val) :
    FlushLimbInvariant baseRaw (flushRawCell currentRaw slot limb)
      baseSums (flushSumCell currentSums slot limb nextSum)
      slot.val (limb.val + 1) := by
  rcases invariant with ⟨sumsCanonical, rawExact, sumsExact⟩
  refine ⟨?_, ?_, ?_⟩
  · intro row rowBound column columnBound
    by_cases sameRow : row = slot.val
    · by_cases sameColumn : column = limb.val
      · subst row
        subst column
        rw [sumCellFlushSame currentSums slot limb nextSum
          slotBound limbBound]
        exact nextSumCanonical
      · rw [sumCellFlushFrame currentSums slot limb nextSum row column
          rowBound columnBound (Or.inr sameColumn)]
        exact sumsCanonical row rowBound column columnBound
    · rw [sumCellFlushFrame currentSums slot limb nextSum row column
        rowBound columnBound (Or.inl sameRow)]
      exact sumsCanonical row rowBound column columnBound
  · intro row rowBound column columnBound
    by_cases sameRow : row = slot.val
    · by_cases sameColumn : column = limb.val
      · subst row
        subst column
        rw [rawCellFlushSame currentRaw slot limb slotBound limbBound]
        simp
      · rw [rawCellFlushFrame currentRaw slot limb row column rowBound
          columnBound (Or.inr sameColumn)]
        have old := rawExact row rowBound column columnBound
        rw [old]
        by_cases before : column < limb.val
        · rw [if_pos ⟨sameRow, before⟩, if_pos ⟨sameRow, by omega⟩]
        · rw [if_neg (by simp [sameRow, before]),
            if_neg (by simp [sameRow]; omega)]
    · rw [rawCellFlushFrame currentRaw slot limb row column rowBound
        columnBound (Or.inl sameRow)]
      have old := rawExact row rowBound column columnBound
      rw [old]
      simp [sameRow]
  · intro row rowBound column columnBound
    by_cases sameRow : row = slot.val
    · by_cases sameColumn : column = limb.val
      · subst row
        subst column
        rw [sumCellFlushSame currentSums slot limb nextSum
          slotBound limbBound]
        rw [nextSumExact]
        have oldSum := sumsExact slot.val slotBound limb.val limbBound
        have oldRaw := rawExact slot.val slotBound limb.val limbBound
        rw [if_neg (by omega)] at oldSum oldRaw
        rw [oldSum, oldRaw]
        rw [if_pos ⟨rfl, by omega⟩]
      · rw [sumCellFlushFrame currentSums slot limb nextSum row column
          rowBound columnBound (Or.inr sameColumn)]
        have old := sumsExact row rowBound column columnBound
        rw [old]
        by_cases before : column < limb.val
        · rw [if_pos ⟨sameRow, before⟩, if_pos ⟨sameRow, by omega⟩]
        · rw [if_neg (by simp [sameRow, before]),
            if_neg (by simp [sameRow]; omega)]
    · rw [sumCellFlushFrame currentSums slot limb nextSum row column
        rowBound columnBound (Or.inl sameRow)]
      have old := sumsExact row rowBound column columnBound
      rw [old]
      simp [sameRow]

private theorem generatedFlushLimbBodyActive
    (slot : Std.Usize) (iter : core.ops.range.Range Std.Usize)
    (currentRaw : Array (Array Std.U64 4#usize) 3#usize)
    (currentSums : Array (Array RawM31 4#usize) 3#usize)
    (slotBound : slot.val < 3)
    (active : iter.start.val < iter.end.val) (endExact : iter.end.val = 4)
    (currentSumCanonical :
      GeneratedCanonicalM31 (sumCell currentSums slot.val iter.start.val)) :
    ∃ iter' nextRaw nextSums,
      sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2_loop0.body
          slot iter currentRaw currentSums =
        ok (cont (iter', nextRaw, nextSums)) ∧
      iter'.start.val = iter.start.val + 1 ∧
      iter'.end.val = iter.end.val ∧
      (∃ nextSum,
        nextRaw = flushRawCell currentRaw slot iter.start ∧
        nextSums = flushSumCell currentSums slot iter.start nextSum ∧
        GeneratedCanonicalM31 nextSum ∧
        generatedM31ToExact nextSum =
          generatedM31ToExact
              (sumCell currentSums slot.val iter.start.val) +
            ((rawCell currentRaw slot.val iter.start.val).val : ExactM31)) := by
  have nextSpec := core.iter.range.IteratorRange.next_Usize_some_spec
    iter active
  obtain ⟨⟨option, iter'⟩, nextRun, optionEq, startEq, endEq⟩ :=
    Aeneas.Std.WP.spec_imp_exists nextSpec
  rw [optionEq] at nextRun
  have limbBound : iter.start.val < 4 := by omega
  have sumsRowRead := arrayIndexRun currentSums slot slotBound
  have sumRead := arrayIndexRun currentSums.val[slot.val]! iter.start limbBound
  have rawRowRead := arrayIndexRun currentRaw slot slotBound
  have rawRead := arrayIndexRun currentRaw.val[slot.val]! iter.start limbBound
  obtain ⟨reduced, reduceRun, reducedCanonical, reducedExact⟩ :=
    generated_m31_reduce_u64_corresponds
      (rawCell currentRaw slot.val iter.start.val)
  obtain ⟨nextSum, addRun, nextSumCanonical, nextSumExact⟩ :=
    generated_m31_add_corresponds
      (sumCell currentSums slot.val iter.start.val) reduced
      currentSumCanonical reducedCanonical
  have sumsMut := arrayIndexMutRun currentSums slot slotBound
  have sumUpdate := arrayUpdateRun currentSums.val[slot.val]! iter.start
    nextSum limbBound
  have rawMut := arrayIndexMutRun currentRaw slot slotBound
  have rawUpdate := arrayUpdateRun currentRaw.val[slot.val]! iter.start
    0#u64 limbBound
  refine ⟨iter', flushRawCell currentRaw slot iter.start,
    flushSumCell currentSums slot iter.start nextSum, ?_, startEq,
    congrArg UScalar.val endEq, ⟨nextSum, rfl, rfl, nextSumCanonical, ?_⟩⟩
  · unfold sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2_loop0.body
    rw [nextRun]
    simp only [bind_tc_ok]
    rw [sumsRowRead]
    simp only [bind_tc_ok]
    rw [sumRead]
    simp only [bind_tc_ok]
    rw [rawRowRead]
    simp only [bind_tc_ok]
    rw [rawRead]
    simp only [bind_tc_ok]
    change
      (do
        let reduced1 ← field.M31.reduce_u64
          (rawCell currentRaw slot.val iter.start.val)
        let nextSum1 ← field.M31.add
          (sumCell currentSums slot.val iter.start.val) reduced1
        let (sumRow, sumBack) ← Array.index_mut_usize currentSums slot
        let sumRow1 ← Array.update sumRow iter.start nextSum1
        let (rawRow, rawBack) ← Array.index_mut_usize currentRaw slot
        let rawRow1 ← Array.update rawRow iter.start 0#u64
        ok (cont (iter', rawBack rawRow1, sumBack sumRow1))) = _
    rw [reduceRun]
    simp only [bind_tc_ok]
    rw [addRun]
    simp only [bind_tc_ok]
    rw [sumsMut]
    simp only [bind_tc_ok]
    rw [sumUpdate]
    simp only [bind_tc_ok]
    rw [rawMut]
    simp only [bind_tc_ok]
    rw [rawUpdate]
    rfl
  · change ((nextSum.val : Nat) : ExactM31) = _
    rw [nextSumExact]
    have reducedExact' : ((reduced.val : Nat) : ExactM31) =
        ((rawCell currentRaw slot.val iter.start.val).val : ExactM31) := by
      simpa [generatedM31ToExact] using reducedExact
    rw [reducedExact']
    rfl

theorem generated_line_flush_limb_loop_corresponds
    (baseRaw : Array (Array Std.U64 4#usize) 3#usize)
    (baseSums : Array (Array RawM31 4#usize) 3#usize)
    (slot : Std.Usize) (slotBound : slot.val < 3)
    (baseSumsCanonical : CanonicalLineSums baseSums) :
    sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2_loop0
        { start := 0#usize, «end» := 4#usize } baseRaw baseSums slot
      ⦃ out => FlushLimbInvariant baseRaw out.1 baseSums out.2
        slot.val 4 ⦄ := by
  simp only [sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2_loop0]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize ×
      (Array (Array Std.U64 4#usize) 3#usize ×
        Array (Array RawM31 4#usize) 3#usize) => 4 - state.1.start.val)
    (fun state => state.1.end.val = 4 ∧ state.1.start.val ≤ 4 ∧
      FlushLimbInvariant baseRaw state.2.1 baseSums state.2.2
        slot.val state.1.start.val)
    (fun out : Array (Array Std.U64 4#usize) 3#usize ×
        Array (Array RawM31 4#usize) 3#usize =>
      FlushLimbInvariant baseRaw out.1 baseSums out.2 slot.val 4)
  · rintro ⟨iter, currentRaw, currentSums⟩
      ⟨endExact, startBound, invariant⟩
    dsimp only at endExact startBound invariant ⊢
    by_cases active : iter.start.val < iter.end.val
    · have limbBound : iter.start.val < 4 := by omega
      have currentCanonical := invariant.1 slot.val slotBound
        iter.start.val limbBound
      obtain ⟨iter', nextRaw, nextSums, bodyRun, nextStart, nextEnd,
          nextSum, nextRawEq, nextSumsEq, nextSumCanonical,
          nextSumExact⟩ :=
        generatedFlushLimbBodyActive slot iter currentRaw currentSums
          slotBound active endExact currentCanonical
      rw [bodyRun]
      simp only [Aeneas.Std.WP.spec_ok]
      subst nextRaw
      subst nextSums
      have nextInvariant := flushLimbInvariantStep baseRaw currentRaw
        baseSums currentSums slot iter.start slotBound limbBound nextSum
        nextSumCanonical nextSumExact invariant
      have nextInvariant' : FlushLimbInvariant baseRaw
          (flushRawCell currentRaw slot iter.start) baseSums
          (flushSumCell currentSums slot iter.start nextSum) slot.val
          iter'.start.val := by
        rw [nextStart]
        exact nextInvariant
      refine ⟨⟨?_, ?_, nextInvariant'⟩, ?_⟩
      · rw [nextEnd]
        exact endExact
      · rw [nextStart]
        omega
      · rw [nextStart]
        omega
    · have done : iter.start.val = 4 := by omega
      have nextSpec := core.iter.range.IteratorRange.next_Usize_none_spec
        iter (by omega)
      obtain ⟨⟨option, iter'⟩, nextRun, optionEq, iterEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists nextSpec
      rw [optionEq, iterEq] at nextRun
      unfold sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop2_loop0.body
      rw [nextRun]
      simpa [done] using invariant
  · refine ⟨by norm_num, by norm_num, baseSumsCanonical, ?_, ?_⟩
    · intro row rowBound limb limbBound
      simp
    · intro row rowBound limb limbBound
      simp

#print axioms generated_line_flush_limb_loop_corresponds

end V7CallerCurrentReleaseR26TerminalLineFlushLimb
