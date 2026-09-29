import V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2

/-!
# Source-exact aggregation for released chunk three

The final chunk introduces groups one, three, four, five, and six in that
order.  The state below names the five live aggregation entries so the source
loop can be replayed without reducing the whole generated recurrence.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3

open V7CallerCurrentReleaseR26GroupedRowsTwiceChunks
open V7CallerCurrentReleaseR26GroupedRowsTwiceAggregationStep
open V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0

abbrev RawQM31 := field.QM31

def unique1 : Array Std.U8 16#usize :=
  Array.make 16#usize
    [1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
def unique13 : Array Std.U8 16#usize :=
  Array.make 16#usize
    [1#u8, 3#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
def unique134 : Array Std.U8 16#usize :=
  Array.make 16#usize
    [1#u8, 3#u8, 4#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
def unique1345 : Array Std.U8 16#usize :=
  Array.make 16#usize
    [1#u8, 3#u8, 4#u8, 5#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
def unique13456 : Array Std.U8 16#usize :=
  Array.make 16#usize
    [1#u8, 3#u8, 4#u8, 5#u8, 6#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]

def coefficients (a b c d e : RawQM31) : Array RawQM31 16#usize :=
  Array.make 16#usize
    [a, b, c, d, e, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO]
def counts (a b c d e : Std.U8) : Array Std.U8 16#usize :=
  Array.make 16#usize
    [a, b, c, d, e, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
def firstSlots (a b c d e : Std.U8) : Array Std.U8 16#usize :=
  Array.make 16#usize
    [a, b, c, d, e, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]

private theorem arrayUpdateTo
    {T : Type} {N : Std.Usize} (values output : Array T N)
    (index : Std.Usize) (bound : index.val < N.val) (value : T)
    (setExact : values.set index value = output) :
    Array.update values index value = ok output := by
  rw [← setExact]
  exact arrayUpdateExact values index bound value

private theorem arrayIndexAt
    {T : Type} [Inhabited T] (values : Array T 16#usize)
    (index : Std.Usize) (bound : index.val < 16) (value : T)
    (valueExact : values.val[index.val]! = value) :
    Array.index_usize values index = ok value := by
  rw [arrayIndexExact values index (by simpa using bound), valueExact]

private theorem basisIndexAt
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : RawQM31)
    (index : Std.Usize) (bound : index.val < 16) (value : RawQM31)
    (valueExact :
      ([b0, b1, b2, b3, b4, b5, b6, b7,
        b8, b9, b10, b11, b12, b13, b14, b15] : List RawQM31)[index.val]! = value) :
    Array.index_usize
      (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
      index = ok value := by
  have run := arrayIndexExact
    (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
    index (by simpa using bound)
  change _ = ok (([b0, b1, b2, b3, b4, b5, b6, b7,
    b8, b9, b10, b11, b12, b13, b14, b15] : List RawQM31)[index.val]!) at run
  rwa [valueExact] at run

private theorem chunk3IndexAt
    (index : Std.Usize) (bound : index.val < 16) (value : Std.U8)
    (valueExact : chunk3.val[index.val]! = value) :
    Slice.index_usize chunk3 index = ok value := by
  have run := sliceIndexExact chunk3 index (by simpa [chunk3] using bound)
  rwa [valueExact] at run

private theorem step0
    (basis : Array RawQM31 16#usize) (b0 : RawQM31)
    (basisRun : Array.index_usize basis 0#usize = ok b0) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk3 groups0
      coefficients0 groups0 groups0 0#usize 0#usize =
    ok (cont (unique1,
      coefficients b0 field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO,
      counts 1#u8 0#u8 0#u8 0#u8 0#u8,
      firstSlots 0#u8 0#u8 0#u8 0#u8 0#u8, 1#usize, 1#usize)) := by
  apply aggregationNewStep
    (basis := basis) (chunk := chunk3) (uniqueGroups := groups0)
    (uniqueGroupsOut := unique1) (coefficients := coefficients0)
    (coefficientsOut := coefficients b0 field.QM31.ZERO field.QM31.ZERO
      field.QM31.ZERO field.QM31.ZERO)
    (counts := groups0) (countsOut := counts 1#u8 0#u8 0#u8 0#u8 0#u8)
    (firstSlots := groups0)
    (firstSlotsOut := firstSlots 0#u8 0#u8 0#u8 0#u8 0#u8)
    (uniqueLength := 0#usize) (uniqueLengthOut := 1#usize)
    (slot := 0#usize) (slotOut := 1#usize) (group := 1#u8)
    (slotU8 := 0#u8) (coefficient := b0)
  · decide
  · exact chunk3IndexAt 0#usize (by decide) 1#u8 rfl
  · exact searchEmpty groups0 1#u8
  · apply arrayUpdateTo groups0 unique1 0#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact basisRun
  · apply arrayUpdateTo coefficients0
      (coefficients b0 field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO)
      0#usize (by decide) b0
    apply Subtype.ext; rfl
  · apply arrayUpdateTo groups0 (counts 1#u8 0#u8 0#u8 0#u8 0#u8)
      0#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact castUsizeToU8Exact 0#usize 0#u8 rfl (by decide)
  · apply arrayUpdateTo groups0 (firstSlots 0#u8 0#u8 0#u8 0#u8 0#u8)
      0#usize (by decide) 0#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 0#usize 1#usize rfl (by
      have h := (1#usize).hSize; scalar_tac)
  · exact usizeWrappingSuccExact 0#usize 1#usize rfl (by
      have h := (1#usize).hSize; scalar_tac)

private theorem newGroup3
    (basis : Array RawQM31 16#usize) (b0 b1 : RawQM31)
    (basisRun : Array.index_usize basis 1#usize = ok b1) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk3 unique1
      (coefficients b0 field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO)
      (counts 1#u8 0#u8 0#u8 0#u8 0#u8)
      (firstSlots 0#u8 0#u8 0#u8 0#u8 0#u8) 1#usize 1#usize =
    ok (cont (unique13,
      coefficients b0 b1 field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO,
      counts 1#u8 1#u8 0#u8 0#u8 0#u8,
      firstSlots 0#u8 1#u8 0#u8 0#u8 0#u8, 2#usize, 2#usize)) := by
  apply aggregationNewStep
  · decide
  · exact chunk3IndexAt 1#usize (by decide) 3#u8 rfl
  · apply searchNew1 unique1 3#u8 1#u8
    · exact arrayIndexAt unique1 0#usize (by decide) 1#u8 rfl
    · decide
  · apply arrayUpdateTo unique1 unique13 1#usize (by decide) 3#u8
    apply Subtype.ext; rfl
  · exact basisRun
  · apply arrayUpdateTo
      (coefficients b0 field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO)
      (coefficients b0 b1 field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO)
      1#usize (by decide) b1
    apply Subtype.ext; rfl
  · apply arrayUpdateTo (counts 1#u8 0#u8 0#u8 0#u8 0#u8)
      (counts 1#u8 1#u8 0#u8 0#u8 0#u8) 1#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact castUsizeToU8Exact 1#usize 1#u8 rfl (by decide)
  · apply arrayUpdateTo (firstSlots 0#u8 0#u8 0#u8 0#u8 0#u8)
      (firstSlots 0#u8 1#u8 0#u8 0#u8 0#u8) 1#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 1#usize 2#usize rfl (by
      have h := (2#usize).hSize; scalar_tac)
  · exact usizeWrappingSuccExact 1#usize 2#usize rfl (by
      have h := (2#usize).hSize; scalar_tac)

private theorem newGroup4
    (basis : Array RawQM31 16#usize) (b0 group3 b5 : RawQM31)
    (basisRun : Array.index_usize basis 5#usize = ok b5) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk3 unique13
      (coefficients b0 group3 field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO)
      (counts 1#u8 4#u8 0#u8 0#u8 0#u8)
      (firstSlots 0#u8 1#u8 0#u8 0#u8 0#u8) 2#usize 5#usize =
    ok (cont (unique134,
      coefficients b0 group3 b5 field.QM31.ZERO field.QM31.ZERO,
      counts 1#u8 4#u8 1#u8 0#u8 0#u8,
      firstSlots 0#u8 1#u8 5#u8 0#u8 0#u8, 3#usize, 6#usize)) := by
  apply aggregationNewStep
  · decide
  · exact chunk3IndexAt 5#usize (by decide) 4#u8 rfl
  · apply searchNew2 unique13 4#u8 1#u8 3#u8
    · exact arrayIndexAt unique13 0#usize (by decide) 1#u8 rfl
    · exact arrayIndexAt unique13 1#usize (by decide) 3#u8 rfl
    · decide
    · decide
  · apply arrayUpdateTo unique13 unique134 2#usize (by decide) 4#u8
    apply Subtype.ext; rfl
  · exact basisRun
  · apply arrayUpdateTo
      (coefficients b0 group3 field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO)
      (coefficients b0 group3 b5 field.QM31.ZERO field.QM31.ZERO)
      2#usize (by decide) b5
    apply Subtype.ext; rfl
  · apply arrayUpdateTo (counts 1#u8 4#u8 0#u8 0#u8 0#u8)
      (counts 1#u8 4#u8 1#u8 0#u8 0#u8) 2#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact castUsizeToU8Exact 5#usize 5#u8 rfl (by decide)
  · apply arrayUpdateTo (firstSlots 0#u8 1#u8 0#u8 0#u8 0#u8)
      (firstSlots 0#u8 1#u8 5#u8 0#u8 0#u8) 2#usize (by decide) 5#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 2#usize 3#usize rfl (by
      have h := (3#usize).hSize; scalar_tac)
  · exact usizeWrappingSuccExact 5#usize 6#usize rfl (by
      have h := (6#usize).hSize; scalar_tac)

private theorem newGroup5
    (basis : Array RawQM31 16#usize) (b0 group3 b5 b6 : RawQM31)
    (basisRun : Array.index_usize basis 6#usize = ok b6) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk3 unique134
      (coefficients b0 group3 b5 field.QM31.ZERO field.QM31.ZERO)
      (counts 1#u8 4#u8 1#u8 0#u8 0#u8)
      (firstSlots 0#u8 1#u8 5#u8 0#u8 0#u8) 3#usize 6#usize =
    ok (cont (unique1345, coefficients b0 group3 b5 b6 field.QM31.ZERO,
      counts 1#u8 4#u8 1#u8 1#u8 0#u8,
      firstSlots 0#u8 1#u8 5#u8 6#u8 0#u8, 4#usize, 7#usize)) := by
  apply aggregationNewStep
  · decide
  · exact chunk3IndexAt 6#usize (by decide) 5#u8 rfl
  · apply searchNew3 unique134 5#u8 1#u8 3#u8 4#u8
    · exact arrayIndexAt unique134 0#usize (by decide) 1#u8 rfl
    · exact arrayIndexAt unique134 1#usize (by decide) 3#u8 rfl
    · exact arrayIndexAt unique134 2#usize (by decide) 4#u8 rfl
    · decide
    · decide
    · decide
  · apply arrayUpdateTo unique134 unique1345 3#usize (by decide) 5#u8
    apply Subtype.ext; rfl
  · exact basisRun
  · apply arrayUpdateTo
      (coefficients b0 group3 b5 field.QM31.ZERO field.QM31.ZERO)
      (coefficients b0 group3 b5 b6 field.QM31.ZERO)
      3#usize (by decide) b6
    apply Subtype.ext; rfl
  · apply arrayUpdateTo (counts 1#u8 4#u8 1#u8 0#u8 0#u8)
      (counts 1#u8 4#u8 1#u8 1#u8 0#u8) 3#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact castUsizeToU8Exact 6#usize 6#u8 rfl (by decide)
  · apply arrayUpdateTo (firstSlots 0#u8 1#u8 5#u8 0#u8 0#u8)
      (firstSlots 0#u8 1#u8 5#u8 6#u8 0#u8) 3#usize (by decide) 6#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 3#usize 4#usize rfl (by
      have h := (4#usize).hSize; scalar_tac)
  · exact usizeWrappingSuccExact 6#usize 7#usize rfl (by
      have h := (7#usize).hSize; scalar_tac)

private theorem newGroup6
    (basis : Array RawQM31 16#usize) (b0 group3 b5 b6 b7 : RawQM31)
    (basisRun : Array.index_usize basis 7#usize = ok b7) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk3 unique1345
      (coefficients b0 group3 b5 b6 field.QM31.ZERO)
      (counts 1#u8 4#u8 1#u8 1#u8 0#u8)
      (firstSlots 0#u8 1#u8 5#u8 6#u8 0#u8) 4#usize 7#usize =
    ok (cont (unique13456, coefficients b0 group3 b5 b6 b7,
      counts 1#u8 4#u8 1#u8 1#u8 1#u8,
      firstSlots 0#u8 1#u8 5#u8 6#u8 7#u8, 5#usize, 8#usize)) := by
  apply aggregationNewStep
  · decide
  · exact chunk3IndexAt 7#usize (by decide) 6#u8 rfl
  · apply searchNew4 unique1345 6#u8 1#u8 3#u8 4#u8 5#u8
    · exact arrayIndexAt unique1345 0#usize (by decide) 1#u8 rfl
    · exact arrayIndexAt unique1345 1#usize (by decide) 3#u8 rfl
    · exact arrayIndexAt unique1345 2#usize (by decide) 4#u8 rfl
    · exact arrayIndexAt unique1345 3#usize (by decide) 5#u8 rfl
    · decide
    · decide
    · decide
    · decide
  · apply arrayUpdateTo unique1345 unique13456 4#usize (by decide) 6#u8
    apply Subtype.ext; rfl
  · exact basisRun
  · apply arrayUpdateTo (coefficients b0 group3 b5 b6 field.QM31.ZERO)
      (coefficients b0 group3 b5 b6 b7) 4#usize (by decide) b7
    apply Subtype.ext; rfl
  · apply arrayUpdateTo (counts 1#u8 4#u8 1#u8 1#u8 0#u8)
      (counts 1#u8 4#u8 1#u8 1#u8 1#u8) 4#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact castUsizeToU8Exact 7#usize 7#u8 rfl (by decide)
  · apply arrayUpdateTo (firstSlots 0#u8 1#u8 5#u8 6#u8 0#u8)
      (firstSlots 0#u8 1#u8 5#u8 6#u8 7#u8) 4#usize (by decide) 7#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 4#usize 5#usize rfl (by
      have h := (5#usize).hSize; scalar_tac)
  · exact usizeWrappingSuccExact 7#usize 8#usize rfl (by
      have h := (8#usize).hSize; scalar_tac)

private theorem existingGroup3
    (basis : Array RawQM31 16#usize) (b0 current basisValue output : RawQM31)
    (count countOut : Std.U8) (slot slotOut : Std.Usize)
    (slotActive : slot < 16#usize)
    (groupRun : Slice.index_usize chunk3 slot = ok 3#u8)
    (basisRun : Array.index_usize basis slot = ok basisValue)
    (addRun : field.QM31.add current basisValue = ok output)
    (countSucc : Std.U8.wrapping_add count 1#u8 = countOut)
    (slotSucc : Std.Usize.wrapping_add slot 1#usize = slotOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk3 unique13
      (coefficients b0 current field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO)
      (counts 1#u8 count 0#u8 0#u8 0#u8)
      (firstSlots 0#u8 1#u8 0#u8 0#u8 0#u8) 2#usize slot =
    ok (cont (unique13,
      coefficients b0 output field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO,
      counts 1#u8 countOut 0#u8 0#u8 0#u8,
      firstSlots 0#u8 1#u8 0#u8 0#u8 0#u8, 2#usize, slotOut)) := by
  apply aggregationExistingStep
    (position := 1#usize) (group := 3#u8) (count := count)
    (countOut := countOut) (coefficient := current)
    (basisValue := basisValue) (coefficientOut := output)
  · exact slotActive
  · exact groupRun
  · apply searchAt1 unique13 2#usize 3#u8 1#u8
      (by decide) (by decide)
      (arrayIndexAt unique13 0#usize (by decide) 1#u8 rfl) (by decide)
      (arrayIndexAt unique13 1#usize (by decide) 3#u8 rfl)
  · decide
  · exact arrayIndexAt
      (coefficients b0 current field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO)
      1#usize (by decide) current rfl
  · exact basisRun
  · exact addRun
  · apply arrayUpdateTo
      (coefficients b0 current field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO)
      (coefficients b0 output field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO)
      1#usize (by decide) output
    apply Subtype.ext; rfl
  · exact arrayIndexAt (counts 1#u8 count 0#u8 0#u8 0#u8)
      1#usize (by decide) count rfl
  · exact countSucc
  · apply arrayUpdateTo (counts 1#u8 count 0#u8 0#u8 0#u8)
      (counts 1#u8 countOut 0#u8 0#u8 0#u8) 1#usize (by decide) countOut
    apply Subtype.ext; rfl
  · exact slotSucc

private theorem existingGroup6
    (basis : Array RawQM31 16#usize)
    (b0 group3 b5 b6 current basisValue output : RawQM31)
    (count countOut : Std.U8) (slot slotOut : Std.Usize)
    (slotActive : slot < 16#usize)
    (groupRun : Slice.index_usize chunk3 slot = ok 6#u8)
    (basisRun : Array.index_usize basis slot = ok basisValue)
    (addRun : field.QM31.add current basisValue = ok output)
    (countSucc : Std.U8.wrapping_add count 1#u8 = countOut)
    (slotSucc : Std.Usize.wrapping_add slot 1#usize = slotOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk3 unique13456
      (coefficients b0 group3 b5 b6 current)
      (counts 1#u8 4#u8 1#u8 1#u8 count)
      (firstSlots 0#u8 1#u8 5#u8 6#u8 7#u8) 5#usize slot =
    ok (cont (unique13456, coefficients b0 group3 b5 b6 output,
      counts 1#u8 4#u8 1#u8 1#u8 countOut,
      firstSlots 0#u8 1#u8 5#u8 6#u8 7#u8, 5#usize, slotOut)) := by
  apply aggregationExistingStep
    (position := 4#usize) (group := 6#u8) (count := count)
    (countOut := countOut) (coefficient := current)
    (basisValue := basisValue) (coefficientOut := output)
  · exact slotActive
  · exact groupRun
  · apply searchAt4 unique13456 5#usize 6#u8 1#u8 3#u8 4#u8 5#u8
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact arrayIndexAt unique13456 0#usize (by decide) 1#u8 rfl
    · exact arrayIndexAt unique13456 1#usize (by decide) 3#u8 rfl
    · exact arrayIndexAt unique13456 2#usize (by decide) 4#u8 rfl
    · exact arrayIndexAt unique13456 3#usize (by decide) 5#u8 rfl
    · decide
    · decide
    · decide
    · decide
    · exact arrayIndexAt unique13456 4#usize (by decide) 6#u8 rfl
  · decide
  · exact arrayIndexAt (coefficients b0 group3 b5 b6 current)
      4#usize (by decide) current rfl
  · exact basisRun
  · exact addRun
  · apply arrayUpdateTo (coefficients b0 group3 b5 b6 current)
      (coefficients b0 group3 b5 b6 output) 4#usize (by decide) output
    apply Subtype.ext; rfl
  · exact arrayIndexAt (counts 1#u8 4#u8 1#u8 1#u8 count)
      4#usize (by decide) count rfl
  · exact countSucc
  · apply arrayUpdateTo (counts 1#u8 4#u8 1#u8 1#u8 count)
      (counts 1#u8 4#u8 1#u8 1#u8 countOut) 4#usize (by decide) countOut
    apply Subtype.ext; rfl
  · exact slotSucc

structure Chunk3CoefficientTrace
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31) : Type where
  c2 : RawQM31
  c3 : RawQM31
  c4 : RawQM31
  d8 : RawQM31
  d9 : RawQM31
  d10 : RawQM31
  d11 : RawQM31
  d12 : RawQM31
  d13 : RawQM31
  d14 : RawQM31
  d15 : RawQM31
  c2Run : field.QM31.add b1 b2 = ok c2
  c3Run : field.QM31.add c2 b3 = ok c3
  c4Run : field.QM31.add c3 b4 = ok c4
  d8Run : field.QM31.add b7 b8 = ok d8
  d9Run : field.QM31.add d8 b9 = ok d9
  d10Run : field.QM31.add d9 b10 = ok d10
  d11Run : field.QM31.add d10 b11 = ok d11
  d12Run : field.QM31.add d11 b12 = ok d12
  d13Run : field.QM31.add d12 b13 = ok d13
  d14Run : field.QM31.add d13 b14 = ok d14
  d15Run : field.QM31.add d14 b15 = ok d15

theorem chunk3_aggregation_exact
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : RawQM31)
    (trace : Chunk3CoefficientTrace
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0
      (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
      chunk3 groups0 coefficients0 groups0 groups0 0#usize 0#usize =
    ok (unique13456, coefficients b0 trace.c4 b5 b6 trace.d15,
      counts 1#u8 4#u8 1#u8 1#u8 9#u8,
      firstSlots 0#u8 1#u8 5#u8 6#u8 7#u8, 5#usize) := by
  let basis := basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  have basisRead (slot : Std.Usize) (bound : slot.val < 16)
      (value : RawQM31)
      (valueExact :
        ([b0, b1, b2, b3, b4, b5, b6, b7,
          b8, b9, b10, b11, b12, b13, b14, b15] : List RawQM31)[slot.val]! = value) :
      Array.index_usize basis slot = ok value := by
    simpa [basis] using basisIndexAt b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
      b11 b12 b13 b14 b15 slot bound value valueExact
  have groupRead (slot : Std.Usize) (bound : slot.val < 16)
      (value : Std.U8) (valueExact : chunk3.val[slot.val]! = value) :
      Slice.index_usize chunk3 slot = ok value :=
    chunk3IndexAt slot bound value valueExact
  have usizeSucc (slot next : Std.Usize) (valueExact : slot.val + 1 = next.val) :
      Std.Usize.wrapping_add slot 1#usize = next :=
    usizeWrappingSuccExact slot next valueExact (by rw [valueExact]; exact next.hSize)
  have u8Succ (count next : Std.U8) (valueExact : count.val + 1 = next.val) :
      Std.U8.wrapping_add count 1#u8 = next :=
    u8WrappingSuccExact count next valueExact (by rw [valueExact]; exact next.hSize)
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0
  rw [loop.eq_1]; dsimp only
  rw [step0 basis b0 (basisRead 0#usize (by decide) b0 rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [newGroup3 basis b0 b1 (basisRead 1#usize (by decide) b1 rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingGroup3 basis b0 b1 b2 trace.c2 1#u8 2#u8 2#usize 3#usize
    (by decide) (groupRead 2#usize (by decide) 3#u8 rfl)
    (basisRead 2#usize (by decide) b2 rfl) trace.c2Run
    (u8Succ 1#u8 2#u8 rfl) (usizeSucc 2#usize 3#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingGroup3 basis b0 trace.c2 b3 trace.c3 2#u8 3#u8 3#usize 4#usize
    (by decide) (groupRead 3#usize (by decide) 3#u8 rfl)
    (basisRead 3#usize (by decide) b3 rfl) trace.c3Run
    (u8Succ 2#u8 3#u8 rfl) (usizeSucc 3#usize 4#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingGroup3 basis b0 trace.c3 b4 trace.c4 3#u8 4#u8 4#usize 5#usize
    (by decide) (groupRead 4#usize (by decide) 3#u8 rfl)
    (basisRead 4#usize (by decide) b4 rfl) trace.c4Run
    (u8Succ 3#u8 4#u8 rfl) (usizeSucc 4#usize 5#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [newGroup4 basis b0 trace.c4 b5
    (basisRead 5#usize (by decide) b5 rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [newGroup5 basis b0 trace.c4 b5 b6
    (basisRead 6#usize (by decide) b6 rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [newGroup6 basis b0 trace.c4 b5 b6 b7
    (basisRead 7#usize (by decide) b7 rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingGroup6 basis b0 trace.c4 b5 b6 b7 b8 trace.d8
    1#u8 2#u8 8#usize 9#usize (by decide)
    (groupRead 8#usize (by decide) 6#u8 rfl)
    (basisRead 8#usize (by decide) b8 rfl) trace.d8Run
    (u8Succ 1#u8 2#u8 rfl) (usizeSucc 8#usize 9#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingGroup6 basis b0 trace.c4 b5 b6 trace.d8 b9 trace.d9
    2#u8 3#u8 9#usize 10#usize (by decide)
    (groupRead 9#usize (by decide) 6#u8 rfl)
    (basisRead 9#usize (by decide) b9 rfl) trace.d9Run
    (u8Succ 2#u8 3#u8 rfl) (usizeSucc 9#usize 10#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingGroup6 basis b0 trace.c4 b5 b6 trace.d9 b10 trace.d10
    3#u8 4#u8 10#usize 11#usize (by decide)
    (groupRead 10#usize (by decide) 6#u8 rfl)
    (basisRead 10#usize (by decide) b10 rfl) trace.d10Run
    (u8Succ 3#u8 4#u8 rfl) (usizeSucc 10#usize 11#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingGroup6 basis b0 trace.c4 b5 b6 trace.d10 b11 trace.d11
    4#u8 5#u8 11#usize 12#usize (by decide)
    (groupRead 11#usize (by decide) 6#u8 rfl)
    (basisRead 11#usize (by decide) b11 rfl) trace.d11Run
    (u8Succ 4#u8 5#u8 rfl) (usizeSucc 11#usize 12#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingGroup6 basis b0 trace.c4 b5 b6 trace.d11 b12 trace.d12
    5#u8 6#u8 12#usize 13#usize (by decide)
    (groupRead 12#usize (by decide) 6#u8 rfl)
    (basisRead 12#usize (by decide) b12 rfl) trace.d12Run
    (u8Succ 5#u8 6#u8 rfl) (usizeSucc 12#usize 13#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingGroup6 basis b0 trace.c4 b5 b6 trace.d12 b13 trace.d13
    6#u8 7#u8 13#usize 14#usize (by decide)
    (groupRead 13#usize (by decide) 6#u8 rfl)
    (basisRead 13#usize (by decide) b13 rfl) trace.d13Run
    (u8Succ 6#u8 7#u8 rfl) (usizeSucc 13#usize 14#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingGroup6 basis b0 trace.c4 b5 b6 trace.d13 b14 trace.d14
    7#u8 8#u8 14#usize 15#usize (by decide)
    (groupRead 14#usize (by decide) 6#u8 rfl)
    (basisRead 14#usize (by decide) b14 rfl) trace.d14Run
    (u8Succ 7#u8 8#u8 rfl) (usizeSucc 14#usize 15#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingGroup6 basis b0 trace.c4 b5 b6 trace.d14 b15 trace.d15
    8#u8 9#u8 15#usize 16#usize (by decide)
    (groupRead 15#usize (by decide) 6#u8 rfl)
    (basisRead 15#usize (by decide) b15 rfl) trace.d15Run
    (u8Succ 8#u8 9#u8 rfl) (usizeSucc 15#usize 16#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [aggregationDone basis chunk3 unique13456
    (coefficients b0 trace.c4 b5 b6 trace.d15)
    (counts 1#u8 4#u8 1#u8 1#u8 9#u8)
    (firstSlots 0#u8 1#u8 5#u8 6#u8 7#u8) 5#usize]
#print axioms step0
#print axioms newGroup3
#print axioms newGroup4
#print axioms newGroup5
#print axioms newGroup6
#print axioms existingGroup3
#print axioms existingGroup6
#print axioms chunk3_aggregation_exact

end V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3
