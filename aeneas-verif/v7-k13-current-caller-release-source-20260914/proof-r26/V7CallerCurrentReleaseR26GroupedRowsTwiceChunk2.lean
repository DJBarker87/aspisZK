import V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1

/-!
# Source-exact aggregation for released chunk two

Chunk two introduces groups two and zero after eleven group-one slots, then
revisits all three groups.  Each source-loop edge remains explicit.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2

open V7CallerCurrentReleaseR26GroupedRowsTwiceChunks
open V7CallerCurrentReleaseR26GroupedRowsTwiceAggregationStep
open V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0

abbrev RawQM31 := field.QM31

def uniqueA : Array Std.U8 16#usize :=
  Array.make 16#usize
    [1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
def uniqueAB : Array Std.U8 16#usize :=
  Array.make 16#usize
    [1#u8, 2#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
def uniqueABC : Array Std.U8 16#usize := uniqueAB

def coefficients (a b c : RawQM31) : Array RawQM31 16#usize :=
  Array.make 16#usize
    [a, b, c, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO]
def counts (a b c : Std.U8) : Array Std.U8 16#usize :=
  Array.make 16#usize
    [a, b, c, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
def firstSlots (a b c : Std.U8) : Array Std.U8 16#usize :=
  Array.make 16#usize
    [a, b, c, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
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

private theorem chunk2IndexAt
    (index : Std.Usize) (bound : index.val < 16) (value : Std.U8)
    (valueExact : chunk2.val[index.val]! = value) :
    Slice.index_usize chunk2 index = ok value := by
  have run := sliceIndexExact chunk2 index (by simpa [chunk2] using bound)
  rwa [valueExact] at run

private theorem existingAt
    (basis : Array RawQM31 16#usize)
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength position : Std.Usize)
    (a b c aOut bOut cOut : RawQM31)
    (ca cb cc caOut cbOut ccOut : Std.U8) (sa sb sc : Std.U8)
    (slot slotOut : Std.Usize) (group : Std.U8)
    (current basisValue output : RawQM31) (count countOut : Std.U8)
    (slotActive : slot < 16#usize)
    (groupRun : Slice.index_usize chunk2 slot = ok group)
    (searchRun : sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
      uniqueGroups uniqueLength group 0#usize = ok position)
    (positionExisting : position ≠ uniqueLength)
    (coefficientRead : Array.index_usize (coefficients a b c) position = ok current)
    (basisRun : Array.index_usize basis slot = ok basisValue)
    (addRun : field.QM31.add current basisValue = ok output)
    (coefficientUpdate : Array.update (coefficients a b c) position output =
      ok (coefficients aOut bOut cOut))
    (countRead : Array.index_usize (counts ca cb cc) position = ok count)
    (countSucc : Std.U8.wrapping_add count 1#u8 = countOut)
    (countUpdate : Array.update (counts ca cb cc) position countOut =
      ok (counts caOut cbOut ccOut))
    (slotSucc : Std.Usize.wrapping_add slot 1#usize = slotOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk2 uniqueGroups
      (coefficients a b c) (counts ca cb cc) (firstSlots sa sb sc)
      uniqueLength slot =
    ok (cont (uniqueGroups, coefficients aOut bOut cOut,
      counts caOut cbOut ccOut, firstSlots sa sb sc, uniqueLength, slotOut)) := by
  exact aggregationExistingStep basis chunk2 uniqueGroups
    (coefficients a b c) (coefficients aOut bOut cOut)
    (counts ca cb cc) (counts caOut cbOut ccOut) (firstSlots sa sb sc)
    uniqueLength position slot slotOut group count countOut current basisValue output
    slotActive groupRun searchRun positionExisting coefficientRead basisRun addRun
    coefficientUpdate countRead countSucc countUpdate slotSucc

private theorem step0
    (basis : Array RawQM31 16#usize) (b0 : RawQM31)
    (basisRun : Array.index_usize basis 0#usize = ok b0) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk2 groups0
      coefficients0 groups0 groups0 0#usize 0#usize =
    ok (cont (uniqueA, coefficients b0 field.QM31.ZERO field.QM31.ZERO,
      counts 1#u8 0#u8 0#u8, firstSlots 0#u8 0#u8 0#u8,
      1#usize, 1#usize)) := by
  apply aggregationNewStep
    (basis := basis) (chunk := chunk2) (uniqueGroups := groups0)
    (uniqueGroupsOut := uniqueA) (coefficients := coefficients0)
    (coefficientsOut := coefficients b0 field.QM31.ZERO field.QM31.ZERO)
    (counts := groups0) (countsOut := counts 1#u8 0#u8 0#u8)
    (firstSlots := groups0) (firstSlotsOut := firstSlots 0#u8 0#u8 0#u8)
    (uniqueLength := 0#usize) (uniqueLengthOut := 1#usize)
    (slot := 0#usize) (slotOut := 1#usize) (group := 1#u8)
    (slotU8 := 0#u8) (coefficient := b0)
  · decide
  · exact chunk2IndexAt 0#usize (by decide) 1#u8 rfl
  · exact searchEmpty groups0 1#u8
  · apply arrayUpdateTo groups0 uniqueA 0#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact basisRun
  · apply arrayUpdateTo coefficients0
      (coefficients b0 field.QM31.ZERO field.QM31.ZERO) 0#usize (by decide) b0
    apply Subtype.ext; rfl
  · apply arrayUpdateTo groups0 (counts 1#u8 0#u8 0#u8)
      0#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact castUsizeToU8Exact 0#usize 0#u8 rfl (by decide)
  · apply arrayUpdateTo groups0 (firstSlots 0#u8 0#u8 0#u8)
      0#usize (by decide) 0#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 0#usize 1#usize rfl (by
      have h := (1#usize).hSize; scalar_tac)
  · exact usizeWrappingSuccExact 0#usize 1#usize rfl (by
      have h := (1#usize).hSize; scalar_tac)

private theorem newGroup2
    (basis : Array RawQM31 16#usize) (a b11 : RawQM31)
    (basisRun : Array.index_usize basis 11#usize = ok b11) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk2 uniqueA
      (coefficients a field.QM31.ZERO field.QM31.ZERO) (counts 11#u8 0#u8 0#u8)
      (firstSlots 0#u8 0#u8 0#u8) 1#usize 11#usize =
    ok (cont (uniqueAB, coefficients a b11 field.QM31.ZERO,
      counts 11#u8 1#u8 0#u8, firstSlots 0#u8 11#u8 0#u8,
      2#usize, 12#usize)) := by
  apply aggregationNewStep
    (basis := basis) (chunk := chunk2) (uniqueGroups := uniqueA)
    (uniqueGroupsOut := uniqueAB)
    (coefficients := coefficients a field.QM31.ZERO field.QM31.ZERO)
    (coefficientsOut := coefficients a b11 field.QM31.ZERO)
    (counts := counts 11#u8 0#u8 0#u8) (countsOut := counts 11#u8 1#u8 0#u8)
    (firstSlots := firstSlots 0#u8 0#u8 0#u8)
    (firstSlotsOut := firstSlots 0#u8 11#u8 0#u8)
    (uniqueLength := 1#usize) (uniqueLengthOut := 2#usize)
    (slot := 11#usize) (slotOut := 12#usize) (group := 2#u8)
    (slotU8 := 11#u8) (coefficient := b11)
  · decide
  · exact chunk2IndexAt 11#usize (by decide) 2#u8 rfl
  · apply searchNew1 uniqueA 2#u8 1#u8
    · exact arrayIndexAt uniqueA 0#usize (by decide) 1#u8 rfl
    · decide
  · apply arrayUpdateTo uniqueA uniqueAB 1#usize (by decide) 2#u8
    apply Subtype.ext; rfl
  · exact basisRun
  · apply arrayUpdateTo (coefficients a field.QM31.ZERO field.QM31.ZERO)
      (coefficients a b11 field.QM31.ZERO) 1#usize (by decide) b11
    apply Subtype.ext; rfl
  · apply arrayUpdateTo (counts 11#u8 0#u8 0#u8)
      (counts 11#u8 1#u8 0#u8) 1#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact castUsizeToU8Exact 11#usize 11#u8 rfl (by decide)
  · apply arrayUpdateTo (firstSlots 0#u8 0#u8 0#u8)
      (firstSlots 0#u8 11#u8 0#u8) 1#usize (by decide) 11#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 1#usize 2#usize rfl (by
      have h := (2#usize).hSize; scalar_tac)
  · exact usizeWrappingSuccExact 11#usize 12#usize rfl (by
      have h := (12#usize).hSize; scalar_tac)

private theorem newGroup0
    (basis : Array RawQM31 16#usize) (a b b12 : RawQM31)
    (basisRun : Array.index_usize basis 12#usize = ok b12) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk2 uniqueAB
      (coefficients a b field.QM31.ZERO) (counts 11#u8 1#u8 0#u8)
      (firstSlots 0#u8 11#u8 0#u8) 2#usize 12#usize =
    ok (cont (uniqueABC, coefficients a b b12, counts 11#u8 1#u8 1#u8,
      firstSlots 0#u8 11#u8 12#u8, 3#usize, 13#usize)) := by
  apply aggregationNewStep
    (basis := basis) (chunk := chunk2) (uniqueGroups := uniqueAB)
    (uniqueGroupsOut := uniqueABC)
    (coefficients := coefficients a b field.QM31.ZERO)
    (coefficientsOut := coefficients a b b12)
    (counts := counts 11#u8 1#u8 0#u8) (countsOut := counts 11#u8 1#u8 1#u8)
    (firstSlots := firstSlots 0#u8 11#u8 0#u8)
    (firstSlotsOut := firstSlots 0#u8 11#u8 12#u8)
    (uniqueLength := 2#usize) (uniqueLengthOut := 3#usize)
    (slot := 12#usize) (slotOut := 13#usize) (group := 0#u8)
    (slotU8 := 12#u8) (coefficient := b12)
  · decide
  · exact chunk2IndexAt 12#usize (by decide) 0#u8 rfl
  · apply searchNew2 uniqueAB 0#u8 1#u8 2#u8
    · exact arrayIndexAt uniqueAB 0#usize (by decide) 1#u8 rfl
    · exact arrayIndexAt uniqueAB 1#usize (by decide) 2#u8 rfl
    · decide
    · decide
  · apply arrayUpdateTo uniqueAB uniqueABC 2#usize (by decide) 0#u8
    apply Subtype.ext; rfl
  · exact basisRun
  · apply arrayUpdateTo (coefficients a b field.QM31.ZERO)
      (coefficients a b b12) 2#usize (by decide) b12
    apply Subtype.ext; rfl
  · apply arrayUpdateTo (counts 11#u8 1#u8 0#u8)
      (counts 11#u8 1#u8 1#u8) 2#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact castUsizeToU8Exact 12#usize 12#u8 rfl (by decide)
  · apply arrayUpdateTo (firstSlots 0#u8 11#u8 0#u8)
      (firstSlots 0#u8 11#u8 12#u8) 2#usize (by decide) 12#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 2#usize 3#usize rfl (by
      have h := (3#usize).hSize; scalar_tac)
  · exact usizeWrappingSuccExact 12#usize 13#usize rfl (by
      have h := (13#usize).hSize; scalar_tac)

private theorem existingAt0
    (basis : Array RawQM31 16#usize)
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength : Std.Usize)
    (a b c output basisValue : RawQM31) (ca cb cc caOut : Std.U8)
    (sa sb sc : Std.U8) (slot slotOut : Std.Usize)
    (slotActive : slot < 16#usize)
    (groupRun : Slice.index_usize chunk2 slot = ok 1#u8)
    (searchRun : sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
      uniqueGroups uniqueLength 1#u8 0#usize = ok 0#usize)
    (positionExisting : 0#usize ≠ uniqueLength)
    (basisRun : Array.index_usize basis slot = ok basisValue)
    (addRun : field.QM31.add a basisValue = ok output)
    (countSucc : Std.U8.wrapping_add ca 1#u8 = caOut)
    (slotSucc : Std.Usize.wrapping_add slot 1#usize = slotOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk2 uniqueGroups
      (coefficients a b c) (counts ca cb cc) (firstSlots sa sb sc)
      uniqueLength slot =
    ok (cont (uniqueGroups, coefficients output b c, counts caOut cb cc,
      firstSlots sa sb sc, uniqueLength, slotOut)) := by
  apply existingAt basis uniqueGroups uniqueLength 0#usize
    a b c output b c ca cb cc caOut cb cc sa sb sc slot slotOut
    1#u8 a basisValue output ca caOut
  · exact slotActive
  · exact groupRun
  · exact searchRun
  · exact positionExisting
  · exact arrayIndexAt (coefficients a b c) 0#usize (by decide) a rfl
  · exact basisRun
  · exact addRun
  · apply arrayUpdateTo (coefficients a b c) (coefficients output b c)
      0#usize (by decide) output
    apply Subtype.ext; rfl
  · exact arrayIndexAt (counts ca cb cc) 0#usize (by decide) ca rfl
  · exact countSucc
  · apply arrayUpdateTo (counts ca cb cc) (counts caOut cb cc)
      0#usize (by decide) caOut
    apply Subtype.ext; rfl
  · exact slotSucc

private theorem existingAt1
    (basis : Array RawQM31 16#usize)
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength : Std.Usize)
    (a b c output basisValue : RawQM31) (ca cb cc cbOut : Std.U8)
    (sa sb sc : Std.U8) (slot slotOut : Std.Usize)
    (slotActive : slot < 16#usize)
    (groupRun : Slice.index_usize chunk2 slot = ok 2#u8)
    (searchRun : sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
      uniqueGroups uniqueLength 2#u8 0#usize = ok 1#usize)
    (positionExisting : 1#usize ≠ uniqueLength)
    (basisRun : Array.index_usize basis slot = ok basisValue)
    (addRun : field.QM31.add b basisValue = ok output)
    (countSucc : Std.U8.wrapping_add cb 1#u8 = cbOut)
    (slotSucc : Std.Usize.wrapping_add slot 1#usize = slotOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk2 uniqueGroups
      (coefficients a b c) (counts ca cb cc) (firstSlots sa sb sc)
      uniqueLength slot =
    ok (cont (uniqueGroups, coefficients a output c, counts ca cbOut cc,
      firstSlots sa sb sc, uniqueLength, slotOut)) := by
  apply existingAt basis uniqueGroups uniqueLength 1#usize
    a b c a output c ca cb cc ca cbOut cc sa sb sc slot slotOut
    2#u8 b basisValue output cb cbOut
  · exact slotActive
  · exact groupRun
  · exact searchRun
  · exact positionExisting
  · exact arrayIndexAt (coefficients a b c) 1#usize (by decide) b rfl
  · exact basisRun
  · exact addRun
  · apply arrayUpdateTo (coefficients a b c) (coefficients a output c)
      1#usize (by decide) output
    apply Subtype.ext; rfl
  · exact arrayIndexAt (counts ca cb cc) 1#usize (by decide) cb rfl
  · exact countSucc
  · apply arrayUpdateTo (counts ca cb cc) (counts ca cbOut cc)
      1#usize (by decide) cbOut
    apply Subtype.ext; rfl
  · exact slotSucc

private theorem existingAt2
    (basis : Array RawQM31 16#usize)
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength : Std.Usize)
    (a b c output basisValue : RawQM31) (ca cb cc ccOut : Std.U8)
    (sa sb sc : Std.U8) (slot slotOut : Std.Usize)
    (slotActive : slot < 16#usize)
    (groupRun : Slice.index_usize chunk2 slot = ok 0#u8)
    (searchRun : sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
      uniqueGroups uniqueLength 0#u8 0#usize = ok 2#usize)
    (positionExisting : 2#usize ≠ uniqueLength)
    (basisRun : Array.index_usize basis slot = ok basisValue)
    (addRun : field.QM31.add c basisValue = ok output)
    (countSucc : Std.U8.wrapping_add cc 1#u8 = ccOut)
    (slotSucc : Std.Usize.wrapping_add slot 1#usize = slotOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk2 uniqueGroups
      (coefficients a b c) (counts ca cb cc) (firstSlots sa sb sc)
      uniqueLength slot =
    ok (cont (uniqueGroups, coefficients a b output, counts ca cb ccOut,
      firstSlots sa sb sc, uniqueLength, slotOut)) := by
  apply existingAt basis uniqueGroups uniqueLength 2#usize
    a b c a b output ca cb cc ca cb ccOut sa sb sc slot slotOut
    0#u8 c basisValue output cc ccOut
  · exact slotActive
  · exact groupRun
  · exact searchRun
  · exact positionExisting
  · exact arrayIndexAt (coefficients a b c) 2#usize (by decide) c rfl
  · exact basisRun
  · exact addRun
  · apply arrayUpdateTo (coefficients a b c) (coefficients a b output)
      2#usize (by decide) output
    apply Subtype.ext; rfl
  · exact arrayIndexAt (counts ca cb cc) 2#usize (by decide) cc rfl
  · exact countSucc
  · apply arrayUpdateTo (counts ca cb cc) (counts ca cb ccOut)
      2#usize (by decide) ccOut
    apply Subtype.ext; rfl
  · exact slotSucc

structure Chunk2CoefficientTrace
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31) : Type where
  c1 : RawQM31
  c2 : RawQM31
  c3 : RawQM31
  c4 : RawQM31
  c5 : RawQM31
  c6 : RawQM31
  c7 : RawQM31
  c8 : RawQM31
  c9 : RawQM31
  c10 : RawQM31
  d13 : RawQM31
  e14 : RawQM31
  c15 : RawQM31
  c1Run : field.QM31.add b0 b1 = ok c1
  c2Run : field.QM31.add c1 b2 = ok c2
  c3Run : field.QM31.add c2 b3 = ok c3
  c4Run : field.QM31.add c3 b4 = ok c4
  c5Run : field.QM31.add c4 b5 = ok c5
  c6Run : field.QM31.add c5 b6 = ok c6
  c7Run : field.QM31.add c6 b7 = ok c7
  c8Run : field.QM31.add c7 b8 = ok c8
  c9Run : field.QM31.add c8 b9 = ok c9
  c10Run : field.QM31.add c9 b10 = ok c10
  d13Run : field.QM31.add b11 b13 = ok d13
  e14Run : field.QM31.add b12 b14 = ok e14
  c15Run : field.QM31.add c10 b15 = ok c15

theorem chunk2_aggregation_exact
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31)
    (trace : Chunk2CoefficientTrace
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0
      (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
      chunk2 groups0 coefficients0 groups0 groups0 0#usize 0#usize =
    ok (uniqueABC, coefficients trace.c15 trace.d13 trace.e14,
      counts 12#u8 2#u8 2#u8, firstSlots 0#u8 11#u8 12#u8, 3#usize) := by
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
      (value : Std.U8) (valueExact : chunk2.val[slot.val]! = value) :
      Slice.index_usize chunk2 slot = ok value :=
    chunk2IndexAt slot bound value valueExact
  have usizeSucc (slot next : Std.Usize) (valueExact : slot.val + 1 = next.val) :
      Std.Usize.wrapping_add slot 1#usize = next :=
    usizeWrappingSuccExact slot next valueExact (by rw [valueExact]; exact next.hSize)
  have u8Succ (count next : Std.U8) (valueExact : count.val + 1 = next.val) :
      Std.U8.wrapping_add count 1#u8 = next :=
    u8WrappingSuccExact count next valueExact (by rw [valueExact]; exact next.hSize)
  have readA0 : Array.index_usize uniqueA 0#usize = ok 1#u8 :=
    arrayIndexAt uniqueA 0#usize (by decide) 1#u8 rfl
  have searchA : sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
      uniqueA 1#usize 1#u8 0#usize = ok 0#usize :=
    searchAt0 uniqueA 1#usize 1#u8 (by decide) readA0
  have read0 : Array.index_usize uniqueABC 0#usize = ok 1#u8 :=
    arrayIndexAt uniqueABC 0#usize (by decide) 1#u8 rfl
  have read1 : Array.index_usize uniqueABC 1#usize = ok 2#u8 :=
    arrayIndexAt uniqueABC 1#usize (by decide) 2#u8 rfl
  have read2 : Array.index_usize uniqueABC 2#usize = ok 0#u8 :=
    arrayIndexAt uniqueABC 2#usize (by decide) 0#u8 rfl
  have search0 : sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
      uniqueABC 3#usize 1#u8 0#usize = ok 0#usize :=
    searchAt0 uniqueABC 3#usize 1#u8 (by decide) read0
  have search1 : sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
      uniqueABC 3#usize 2#u8 0#usize = ok 1#usize :=
    searchAt1 uniqueABC 3#usize 2#u8 1#u8 (by decide) (by decide)
      read0 (by decide) read1
  have search2 : sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
      uniqueABC 3#usize 0#u8 0#usize = ok 2#usize :=
    searchAt2 uniqueABC 3#usize 0#u8 1#u8 2#u8
      (by decide) (by decide) (by decide) read0 read1
      (by decide) (by decide) read2
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0
  rw [loop.eq_1]; dsimp only
  rw [step0 basis b0 (basisRead 0#usize (by decide) b0 rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize b0 field.QM31.ZERO field.QM31.ZERO
    trace.c1 b1 1#u8 0#u8 0#u8 2#u8 0#u8 0#u8 0#u8 1#usize 2#usize
    (by decide) (groupRead 1#usize (by decide) 1#u8 rfl) searchA (by decide)
    (basisRead 1#usize (by decide) b1 rfl) trace.c1Run
    (u8Succ 1#u8 2#u8 rfl) (usizeSucc 1#usize 2#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize trace.c1 field.QM31.ZERO field.QM31.ZERO
    trace.c2 b2 2#u8 0#u8 0#u8 3#u8 0#u8 0#u8 0#u8 2#usize 3#usize
    (by decide) (groupRead 2#usize (by decide) 1#u8 rfl) searchA (by decide)
    (basisRead 2#usize (by decide) b2 rfl) trace.c2Run
    (u8Succ 2#u8 3#u8 rfl) (usizeSucc 2#usize 3#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize trace.c2 field.QM31.ZERO field.QM31.ZERO
    trace.c3 b3 3#u8 0#u8 0#u8 4#u8 0#u8 0#u8 0#u8 3#usize 4#usize
    (by decide) (groupRead 3#usize (by decide) 1#u8 rfl) searchA (by decide)
    (basisRead 3#usize (by decide) b3 rfl) trace.c3Run
    (u8Succ 3#u8 4#u8 rfl) (usizeSucc 3#usize 4#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize trace.c3 field.QM31.ZERO field.QM31.ZERO
    trace.c4 b4 4#u8 0#u8 0#u8 5#u8 0#u8 0#u8 0#u8 4#usize 5#usize
    (by decide) (groupRead 4#usize (by decide) 1#u8 rfl) searchA (by decide)
    (basisRead 4#usize (by decide) b4 rfl) trace.c4Run
    (u8Succ 4#u8 5#u8 rfl) (usizeSucc 4#usize 5#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize trace.c4 field.QM31.ZERO field.QM31.ZERO
    trace.c5 b5 5#u8 0#u8 0#u8 6#u8 0#u8 0#u8 0#u8 5#usize 6#usize
    (by decide) (groupRead 5#usize (by decide) 1#u8 rfl) searchA (by decide)
    (basisRead 5#usize (by decide) b5 rfl) trace.c5Run
    (u8Succ 5#u8 6#u8 rfl) (usizeSucc 5#usize 6#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize trace.c5 field.QM31.ZERO field.QM31.ZERO
    trace.c6 b6 6#u8 0#u8 0#u8 7#u8 0#u8 0#u8 0#u8 6#usize 7#usize
    (by decide) (groupRead 6#usize (by decide) 1#u8 rfl) searchA (by decide)
    (basisRead 6#usize (by decide) b6 rfl) trace.c6Run
    (u8Succ 6#u8 7#u8 rfl) (usizeSucc 6#usize 7#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize trace.c6 field.QM31.ZERO field.QM31.ZERO
    trace.c7 b7 7#u8 0#u8 0#u8 8#u8 0#u8 0#u8 0#u8 7#usize 8#usize
    (by decide) (groupRead 7#usize (by decide) 1#u8 rfl) searchA (by decide)
    (basisRead 7#usize (by decide) b7 rfl) trace.c7Run
    (u8Succ 7#u8 8#u8 rfl) (usizeSucc 7#usize 8#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize trace.c7 field.QM31.ZERO field.QM31.ZERO
    trace.c8 b8 8#u8 0#u8 0#u8 9#u8 0#u8 0#u8 0#u8 8#usize 9#usize
    (by decide) (groupRead 8#usize (by decide) 1#u8 rfl) searchA (by decide)
    (basisRead 8#usize (by decide) b8 rfl) trace.c8Run
    (u8Succ 8#u8 9#u8 rfl) (usizeSucc 8#usize 9#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize trace.c8 field.QM31.ZERO field.QM31.ZERO
    trace.c9 b9 9#u8 0#u8 0#u8 10#u8 0#u8 0#u8 0#u8 9#usize 10#usize
    (by decide) (groupRead 9#usize (by decide) 1#u8 rfl) searchA (by decide)
    (basisRead 9#usize (by decide) b9 rfl) trace.c9Run
    (u8Succ 9#u8 10#u8 rfl) (usizeSucc 9#usize 10#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize trace.c9 field.QM31.ZERO field.QM31.ZERO
    trace.c10 b10 10#u8 0#u8 0#u8 11#u8 0#u8 0#u8 0#u8 10#usize 11#usize
    (by decide) (groupRead 10#usize (by decide) 1#u8 rfl) searchA (by decide)
    (basisRead 10#usize (by decide) b10 rfl) trace.c10Run
    (u8Succ 10#u8 11#u8 rfl) (usizeSucc 10#usize 11#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [newGroup2 basis trace.c10 b11
    (basisRead 11#usize (by decide) b11 rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [newGroup0 basis trace.c10 b11 b12
    (basisRead 12#usize (by decide) b12 rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt1 basis uniqueABC 3#usize trace.c10 b11 b12 trace.d13 b13
    11#u8 1#u8 1#u8 2#u8 0#u8 11#u8 12#u8 13#usize 14#usize
    (by decide) (groupRead 13#usize (by decide) 2#u8 rfl) search1 (by decide)
    (basisRead 13#usize (by decide) b13 rfl) trace.d13Run
    (u8Succ 1#u8 2#u8 rfl) (usizeSucc 13#usize 14#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt2 basis uniqueABC 3#usize trace.c10 trace.d13 b12 trace.e14 b14
    11#u8 2#u8 1#u8 2#u8 0#u8 11#u8 12#u8 14#usize 15#usize
    (by decide) (groupRead 14#usize (by decide) 0#u8 rfl) search2 (by decide)
    (basisRead 14#usize (by decide) b14 rfl) trace.e14Run
    (u8Succ 1#u8 2#u8 rfl) (usizeSucc 14#usize 15#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueABC 3#usize trace.c10 trace.d13 trace.e14
    trace.c15 b15 11#u8 2#u8 2#u8 12#u8 0#u8 11#u8 12#u8 15#usize 16#usize
    (by decide) (groupRead 15#usize (by decide) 1#u8 rfl) search0 (by decide)
    (basisRead 15#usize (by decide) b15 rfl) trace.c15Run
    (u8Succ 11#u8 12#u8 rfl) (usizeSucc 15#usize 16#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [aggregationDone basis chunk2 uniqueABC
    (coefficients trace.c15 trace.d13 trace.e14) (counts 12#u8 2#u8 2#u8)
    (firstSlots 0#u8 11#u8 12#u8) 3#usize]

#print axioms step0
#print axioms newGroup2
#print axioms newGroup0
#print axioms existingAt0
#print axioms existingAt1
#print axioms existingAt2
#print axioms chunk2_aggregation_exact

end V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2
