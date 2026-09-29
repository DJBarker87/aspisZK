import V7CallerCurrentReleaseR26TerminalLineAccumulator

/-!
# Raw product loop for the optimized terminal line accumulator

For one scale limb, the generated loop visits the three line-basis factors
and adds one canonical M31 product to each corresponding U64 cell.  The proof
records the update and its no-wrap condition without unfolding a four-line
chunk.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineRawLoop

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotRawArithmetic
open V7CallerCurrentReleaseR26TerminalLineAccumulator

abbrev RawM31 := field.M31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩

def rawCell
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (slot limb : Nat) : Std.U64 :=
  raw.val[slot]!.val[limb]!

def factorAt (factors : Array RawM31 3#usize) (slot : Nat) : RawM31 :=
  factors.val[slot]!

def limbAt (limbs : Array Std.U32 4#usize) (limb : Nat) : RawM31 :=
  limbs.val[limb]!

def CanonicalLimbs (limbs : Array Std.U32 4#usize) : Prop :=
  ∀ limb, limb < 4 → GeneratedCanonicalM31 (limbAt limbs limb)

def rawAccumulatedValue
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (slot limb : Std.Usize) : Std.U64 :=
  Std.U64.wrapping_add (rawCell raw slot.val limb.val)
    (Std.U64.wrapping_mul
      (UScalar.cast .U64 (limbAt limbs limb.val))
      (UScalar.cast .U64 (factorAt factors slot.val)))

def accumulateRawCell
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (slot limb : Std.Usize) : Array (Array Std.U64 4#usize) 3#usize :=
  raw.set slot
    ((raw.val[slot.val]!).set limb
      (rawAccumulatedValue raw factors limbs slot limb))

def RawSlotUpdateInvariant
    (base current : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (limb processed : Nat) : Prop :=
  ∀ slot, slot < 3 → ∀ column, column < 4 →
    (rawCell current slot column).val =
      if slot < processed ∧ column = limb then
        (rawCell base slot column).val +
          rawM31Product (limbAt limbs limb) (factorAt factors slot)
      else (rawCell base slot column).val

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

private theorem rawAccumulatedValueExact
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (slot limb : Std.Usize)
    (factorCanonical : GeneratedCanonicalM31 (factorAt factors slot.val))
    (limbCanonical : GeneratedCanonicalM31 (limbAt limbs limb.val))
    (bound : (rawCell raw slot.val limb.val).val +
      rawM31Product (limbAt limbs limb.val) (factorAt factors slot.val) <
        2 ^ 64) :
    (rawAccumulatedValue raw factors limbs slot limb).val =
      (rawCell raw slot.val limb.val).val +
        rawM31Product (limbAt limbs limb.val) (factorAt factors slot.val) := by
  unfold rawAccumulatedValue
  exact wrapping_accumulate_exact _ _ _ limbCanonical factorCanonical bound

private theorem rawCellAccumulateSame
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (slot limb : Std.Usize)
    (slotBound : slot.val < 3) (limbBound : limb.val < 4) :
    rawCell (accumulateRawCell raw factors limbs slot limb)
        slot.val limb.val = rawAccumulatedValue raw factors limbs slot limb := by
  unfold rawCell accumulateRawCell
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using slotBound, rfl⟩)]
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using limbBound, rfl⟩)]

private theorem rawCellAccumulateFrame
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (slot limb : Std.Usize) (row column : Nat)
    (rowBound : row < 3) (_columnBound : column < 4)
    (different : row ≠ slot.val ∨ column ≠ limb.val) :
    rawCell (accumulateRawCell raw factors limbs slot limb) row column =
      rawCell raw row column := by
  unfold rawCell accumulateRawCell
  simp only [Array.set_val_eq]
  by_cases sameRow : row = slot.val
  · subst row
    rw [List.set_getElem!_eq _ _ _ _ (by
      exact ⟨by simpa [Array.length_eq] using rowBound, rfl⟩)]
    simp only [Array.set_val_eq]
    rw [List.set_getElem!_ne _ _ _ _ (by omega)]
  · rw [List.set_getElem!_ne _ _ _ _ (by omega)]

private theorem rawSlotUpdateInvariantStep
    (base current : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (slot limb : Std.Usize)
    (slotBound : slot.val < 3) (limbBound : limb.val < 4)
    (factorsCanonical : CanonicalLineFactors factors)
    (limbsCanonical : CanonicalLimbs limbs)
    (invariant : RawSlotUpdateInvariant base current factors limbs
      limb.val slot.val)
    (noOverflow :
      (rawCell base slot.val limb.val).val +
        rawM31Product (limbAt limbs limb.val) (factorAt factors slot.val) <
          2 ^ 64) :
    RawSlotUpdateInvariant base
      (accumulateRawCell current factors limbs slot limb)
      factors limbs limb.val (slot.val + 1) := by
  intro row rowBound column columnBound
  by_cases sameRow : row = slot.val
  · by_cases sameColumn : column = limb.val
    · subst row
      subst column
      rw [rawCellAccumulateSame current factors limbs slot limb
        slotBound limbBound]
      rw [rawAccumulatedValueExact current factors limbs slot limb
        (factorsCanonical slot.val slotBound)
        (limbsCanonical limb.val limbBound)]
      · have old := invariant slot.val slotBound limb.val limbBound
        simp at old
        rw [old]
        simp
      · have old := invariant slot.val slotBound limb.val limbBound
        simp at old
        rw [old]
        exact noOverflow
    · rw [rawCellAccumulateFrame current factors limbs slot limb row column
        rowBound columnBound (Or.inr sameColumn)]
      have old := invariant row rowBound column columnBound
      rw [old]
      simp [sameRow, sameColumn]
  · rw [rawCellAccumulateFrame current factors limbs slot limb row column
      rowBound columnBound (Or.inl sameRow)]
    have old := invariant row rowBound column columnBound
    rw [old]
    by_cases before : row < slot.val
    · have next : row ≤ slot.val := by omega
      simp [before, next]
    · have next : ¬ row ≤ slot.val := by omega
      simp [before, next]

private theorem generatedRawSlotBodyActive
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (limb : Std.Usize) (iter : core.ops.range.Range Std.Usize)
    (raw : Array (Array Std.U64 4#usize) 3#usize)
    (limbBound : limb.val < 4)
    (active : iter.start.val < iter.end.val) (endExact : iter.end.val = 3) :
    ∃ iter',
      sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1_loop0.body
          factors limbs limb iter raw =
        ok (cont (iter', accumulateRawCell raw factors limbs iter.start limb)) ∧
      iter'.start.val = iter.start.val + 1 ∧
      iter'.end.val = iter.end.val := by
  have nextSpec := core.iter.range.IteratorRange.next_Usize_some_spec
    iter active
  obtain ⟨⟨option, iter'⟩, nextRun, optionEq, startEq, endEq⟩ :=
    Aeneas.Std.WP.spec_imp_exists nextSpec
  rw [optionEq] at nextRun
  have slotBound : iter.start.val < 3 := by omega
  have limbRead := arrayIndexRun limbs limb limbBound
  have factorRead := arrayIndexRun factors iter.start slotBound
  have rawRowRead := arrayIndexRun raw iter.start slotBound
  have rawCellRead := arrayIndexRun raw.val[iter.start.val]! limb limbBound
  have rawRowMut := arrayIndexMutRun raw iter.start slotBound
  have rowUpdate := arrayUpdateRun raw.val[iter.start.val]! limb
    (rawAccumulatedValue raw factors limbs iter.start limb) limbBound
  refine ⟨iter', ?_, startEq, congrArg UScalar.val endEq⟩
  unfold sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1_loop0.body
  rw [nextRun]
  simp only [limbRead, factorRead, rawRowRead, rawCellRead, rawRowMut,
    bind_tc_ok, Std.lift, from_u64_u32_eq_cast]
  have valueEq :
      raw.val[iter.start.val]!.val[limb.val]!.wrapping_add
          (Std.U64.wrapping_mul
            (UScalar.cast .U64 limbs.val[limb.val]!)
            (UScalar.cast .U64 factors.val[iter.start.val]!)) =
        rawAccumulatedValue raw factors limbs iter.start limb := by
    simp [rawAccumulatedValue, rawCell, factorAt, limbAt]
  rw [valueEq, rowUpdate]
  rfl

theorem generated_line_raw_slot_loop_corresponds
    (base : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (limb : Std.Usize) (limbBound : limb.val < 4)
    (factorsCanonical : CanonicalLineFactors factors)
    (limbsCanonical : CanonicalLimbs limbs)
    (noOverflow : ∀ slot, slot < 3 →
      (rawCell base slot limb.val).val +
        rawM31Product (limbAt limbs limb.val) (factorAt factors slot) <
          2 ^ 64) :
    sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1_loop0
        { start := 0#usize, «end» := 3#usize } base factors limbs limb
      ⦃ out => RawSlotUpdateInvariant base out factors limbs limb.val 3 ⦄ := by
  simp only [sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1_loop0]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize ×
      Array (Array Std.U64 4#usize) 3#usize => 3 - state.1.start.val)
    (fun state => state.1.end.val = 3 ∧ state.1.start.val ≤ 3 ∧
      RawSlotUpdateInvariant base state.2 factors limbs
        limb.val state.1.start.val)
    (fun out => RawSlotUpdateInvariant base out factors limbs limb.val 3)
  · rintro ⟨iter, current⟩ ⟨endExact, startBound, invariant⟩
    dsimp only at endExact startBound invariant ⊢
    by_cases active : iter.start.val < iter.end.val
    · have slotBound : iter.start.val < 3 := by omega
      obtain ⟨iter', bodyRun, nextStart, nextEnd⟩ :=
        generatedRawSlotBodyActive factors limbs limb iter current
          limbBound active endExact
      rw [bodyRun]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [nextEnd]
        exact endExact
      · rw [nextStart]
        omega
      · rw [nextStart]
        exact rawSlotUpdateInvariantStep base current factors limbs
          iter.start limb slotBound limbBound factorsCanonical
          limbsCanonical invariant (noOverflow iter.start.val slotBound)
      · rw [nextStart]
        omega
    · have done : iter.start.val = 3 := by omega
      have nextSpec := core.iter.range.IteratorRange.next_Usize_none_spec
        iter (by omega)
      obtain ⟨⟨option, iter'⟩, nextRun, optionEq, iterEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists nextSpec
      rw [optionEq, iterEq] at nextRun
      unfold sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1_loop0.body
      rw [nextRun]
      simpa [done] using invariant
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro slot slotBound column columnBound
    simp

#print axioms generated_line_raw_slot_loop_corresponds

end V7CallerCurrentReleaseR26TerminalLineRawLoop
