import V7CallerCurrentReleaseR26GroupedRowsTwiceAggregationStep

/-!
# Source-exact aggregation for released chunk zero

The first released sixteen-row chunk has two group identifiers: group zero in
slots zero and one, and group one in slots two through fifteen.  The proof is
factored into the first three shape-changing transitions and one reusable
existing-group transition.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0

open V7CallerCurrentReleaseR26GroupedRowsTwiceChunks
open V7CallerCurrentReleaseR26GroupedRowsTwiceAggregationStep

abbrev RawQM31 := field.QM31

def basis16
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31) : Array RawQM31 16#usize :=
  Array.make 16#usize
    [b0, b1, b2, b3, b4, b5, b6, b7,
     b8, b9, b10, b11, b12, b13, b14, b15]

def groups0 : Array Std.U8 16#usize := Array.repeat 16#usize 0#u8
def groupsA : Array Std.U8 16#usize :=
  Array.make 16#usize
    [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
def groupsAB : Array Std.U8 16#usize :=
  Array.make 16#usize
    [0#u8, 1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]

def coefficients0 : Array RawQM31 16#usize :=
  Array.repeat 16#usize field.QM31.ZERO
def coefficientsA (a : RawQM31) : Array RawQM31 16#usize :=
  Array.make 16#usize
    [a, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO]
def coefficientsAB (a b : RawQM31) : Array RawQM31 16#usize :=
  Array.make 16#usize
    [a, b, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO]

def countsA (a : Std.U8) : Array Std.U8 16#usize :=
  Array.make 16#usize
    [a, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
def countsAB (a b : Std.U8) : Array Std.U8 16#usize :=
  Array.make 16#usize
    [a, b, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]

def slotsA : Array Std.U8 16#usize := groups0
def slotsAB : Array Std.U8 16#usize :=
  Array.make 16#usize
    [0#u8, 2#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]

private theorem arrayUpdateTo
    {T : Type} {N : Std.Usize} (values output : Array T N)
    (index : Std.Usize) (bound : index.val < N.val) (value : T)
    (setExact : values.set index value = output) :
    Array.update values index value = ok output := by
  rw [← setExact]
  exact arrayUpdateExact values index bound value

private theorem basisIndex0
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31) :
    Array.index_usize
      (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
      0#usize = ok b0 := by
  have run := arrayIndexExact
    (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
    0#usize (by decide)
  change _ = ok (([b0, b1, b2, b3, b4, b5, b6, b7,
    b8, b9, b10, b11, b12, b13, b14, b15] : List RawQM31)[0]!) at run
  exact run

private theorem basisIndex1
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31) :
    Array.index_usize
      (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
      1#usize = ok b1 := by
  have run := arrayIndexExact
    (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
    1#usize (by decide)
  change _ = ok (([b0, b1, b2, b3, b4, b5, b6, b7,
    b8, b9, b10, b11, b12, b13, b14, b15] : List RawQM31)[1]!) at run
  exact run

private theorem basisIndex2
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31) :
    Array.index_usize
      (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
      2#usize = ok b2 := by
  have run := arrayIndexExact
    (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
    2#usize (by decide)
  change _ = ok (([b0, b1, b2, b3, b4, b5, b6, b7,
    b8, b9, b10, b11, b12, b13, b14, b15] : List RawQM31)[2]!) at run
  exact run

private theorem basisIndexAt
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31)
    (index : Std.Usize) (bound : index.val < 16) (value : RawQM31)
    (valueExact :
      ([b0, b1, b2, b3, b4, b5, b6, b7,
        b8, b9, b10, b11, b12, b13, b14, b15] : List RawQM31)[index.val]! =
        value) :
    Array.index_usize
      (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
      index = ok value := by
  have run := arrayIndexExact
    (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
    index (by simpa using bound)
  change _ = ok (([b0, b1, b2, b3, b4, b5, b6, b7,
    b8, b9, b10, b11, b12, b13, b14, b15] : List RawQM31)[index.val]!) at run
  rwa [valueExact] at run

private theorem chunk0IndexAt
    (index : Std.Usize) (bound : index.val < 16) (value : Std.U8)
    (valueExact : chunk0.val[index.val]! = value) :
    Slice.index_usize chunk0 index = ok value := by
  have run := sliceIndexExact chunk0 index (by simpa [chunk0] using bound)
  rwa [valueExact] at run

private theorem groupsAIndex0 : Array.index_usize groupsA 0#usize = ok 0#u8 := by
  have run := arrayIndexExact groupsA 0#usize (by decide)
  change _ = ok (([0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
    0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] : List Std.U8)[0]!) at run
  exact run

private theorem coefficientsAIndex0 (a : RawQM31) :
    Array.index_usize (coefficientsA a) 0#usize = ok a := by
  have run := arrayIndexExact (coefficientsA a) 0#usize (by decide)
  change _ = ok (([a, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
    field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
    field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
    field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
    field.QM31.ZERO] : List RawQM31)[0]!) at run
  exact run

private theorem countsAIndex0 (a : Std.U8) :
    Array.index_usize (countsA a) 0#usize = ok a := by
  have run := arrayIndexExact (countsA a) 0#usize (by decide)
  change _ = ok (([a, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
    0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] : List Std.U8)[0]!) at run
  exact run

private theorem groupsABIndex0 :
    Array.index_usize groupsAB 0#usize = ok 0#u8 := by
  have run := arrayIndexExact groupsAB 0#usize (by decide)
  change _ = ok (([0#u8, 1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
    0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] : List Std.U8)[0]!) at run
  exact run

private theorem groupsABIndex1 :
    Array.index_usize groupsAB 1#usize = ok 1#u8 := by
  have run := arrayIndexExact groupsAB 1#usize (by decide)
  change _ = ok (([0#u8, 1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
    0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] : List Std.U8)[1]!) at run
  exact run

private theorem coefficientsABIndex1 (a b : RawQM31) :
    Array.index_usize (coefficientsAB a b) 1#usize = ok b := by
  have run := arrayIndexExact (coefficientsAB a b) 1#usize (by decide)
  change _ = ok (([a, b, field.QM31.ZERO, field.QM31.ZERO,
    field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
    field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
    field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
    field.QM31.ZERO] : List RawQM31)[1]!) at run
  exact run

private theorem countsABIndex1 (a b : Std.U8) :
    Array.index_usize (countsAB a b) 1#usize = ok b := by
  have run := arrayIndexExact (countsAB a b) 1#usize (by decide)
  change _ = ok (([a, b, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
    0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] : List Std.U8)[1]!) at run
  exact run

private theorem step0
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body
      (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
      chunk0 groups0 coefficients0 groups0 groups0 0#usize 0#usize =
    ok (cont (groupsA, coefficientsA b0, countsA 1#u8, slotsA,
      1#usize, 1#usize)) := by
  apply aggregationNewStep
    (basis := basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
    (chunk := chunk0) (uniqueGroups := groups0)
    (uniqueGroupsOut := groupsA) (coefficients := coefficients0)
    (coefficientsOut := coefficientsA b0) (counts := groups0)
    (countsOut := countsA 1#u8) (firstSlots := groups0)
    (firstSlotsOut := slotsA) (uniqueLength := 0#usize)
    (uniqueLengthOut := 1#usize) (slot := 0#usize) (slotOut := 1#usize)
    (group := 0#u8) (slotU8 := 0#u8) (coefficient := b0)
  · decide
  · simpa [chunk0] using sliceIndexExact chunk0 0#usize (by decide)
  · exact searchEmpty groups0 0#u8
  · apply arrayUpdateTo groups0 groupsA 0#usize (by decide) 0#u8
    apply Subtype.ext; rfl
  · exact basisIndex0 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  · apply arrayUpdateTo coefficients0 (coefficientsA b0) 0#usize
      (by decide) b0
    apply Subtype.ext; rfl
  · apply arrayUpdateTo groups0 (countsA 1#u8) 0#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact castUsizeToU8Exact 0#usize 0#u8 rfl (by decide)
  · apply arrayUpdateTo groups0 slotsA 0#usize (by decide) 0#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 0#usize 1#usize rfl (by
      have h := (1#usize).hSize; scalar_tac)
  · exact usizeWrappingSuccExact 0#usize 1#usize rfl (by
      have h := (1#usize).hSize; scalar_tac)

private theorem step1
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a0 :
      RawQM31)
    (addRun : field.QM31.add b0 b1 = ok a0) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body
      (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
      chunk0 groupsA (coefficientsA b0) (countsA 1#u8) slotsA
      1#usize 1#usize =
    ok (cont (groupsA, coefficientsA a0, countsA 2#u8, slotsA,
      1#usize, 2#usize)) := by
  apply aggregationExistingStep
    (basis := basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
    (chunk := chunk0) (uniqueGroups := groupsA)
    (coefficients := coefficientsA b0) (coefficientsOut := coefficientsA a0)
    (counts := countsA 1#u8) (countsOut := countsA 2#u8)
    (firstSlots := slotsA) (uniqueLength := 1#usize)
    (position := 0#usize) (slot := 1#usize) (slotOut := 2#usize)
    (group := 0#u8) (count := 1#u8) (countOut := 2#u8)
    (coefficient := b0) (basisValue := b1) (coefficientOut := a0)
  · decide
  · simpa [chunk0] using sliceIndexExact chunk0 1#usize (by decide)
  · apply searchAt0 groupsA 1#usize 0#u8 (by decide)
    exact groupsAIndex0
  · decide
  · exact coefficientsAIndex0 b0
  · exact basisIndex1 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  · exact addRun
  · apply arrayUpdateTo (coefficientsA b0) (coefficientsA a0)
      0#usize (by decide) a0
    apply Subtype.ext; rfl
  · exact countsAIndex0 1#u8
  · exact u8WrappingSuccExact 1#u8 2#u8 rfl (by
      have h := (2#u8).hSize; scalar_tac)
  · apply arrayUpdateTo (countsA 1#u8) (countsA 2#u8) 0#usize
      (by decide) 2#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 1#usize 2#usize rfl (by
      have h := (2#usize).hSize; scalar_tac)

private theorem step2
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a0 :
      RawQM31) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body
      (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
      chunk0 groupsA (coefficientsA a0) (countsA 2#u8) slotsA
      1#usize 2#usize =
    ok (cont (groupsAB, coefficientsAB a0 b2, countsAB 2#u8 1#u8,
      slotsAB, 2#usize, 3#usize)) := by
  apply aggregationNewStep
    (basis := basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
    (chunk := chunk0) (uniqueGroups := groupsA)
    (uniqueGroupsOut := groupsAB) (coefficients := coefficientsA a0)
    (coefficientsOut := coefficientsAB a0 b2) (counts := countsA 2#u8)
    (countsOut := countsAB 2#u8 1#u8) (firstSlots := slotsA)
    (firstSlotsOut := slotsAB) (uniqueLength := 1#usize)
    (uniqueLengthOut := 2#usize) (slot := 2#usize) (slotOut := 3#usize)
    (group := 1#u8) (slotU8 := 2#u8) (coefficient := b2)
  · decide
  · simpa [chunk0] using sliceIndexExact chunk0 2#usize (by decide)
  · apply searchNew1 groupsA 1#u8 0#u8
    · exact groupsAIndex0
    · decide
  · apply arrayUpdateTo groupsA groupsAB 1#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact basisIndex2 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  · apply arrayUpdateTo (coefficientsA a0) (coefficientsAB a0 b2)
      1#usize (by decide) b2
    apply Subtype.ext; rfl
  · apply arrayUpdateTo (countsA 2#u8) (countsAB 2#u8 1#u8)
      1#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact castUsizeToU8Exact 2#usize 2#u8 rfl (by decide)
  · apply arrayUpdateTo slotsA slotsAB 1#usize (by decide) 2#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 1#usize 2#usize rfl (by
      have h := (2#usize).hSize; scalar_tac)
  · exact usizeWrappingSuccExact 2#usize 3#usize rfl (by
      have h := (3#usize).hSize; scalar_tac)

private theorem existingGroupBStep
    (basis : Array RawQM31 16#usize) (a current basisValue output : RawQM31)
    (count countOut : Std.U8) (slot slotOut : Std.Usize)
    (slotActive : slot < 16#usize)
    (groupRun : Slice.index_usize chunk0 slot = ok 1#u8)
    (basisRun : Array.index_usize basis slot = ok basisValue)
    (addRun : field.QM31.add current basisValue = ok output)
    (countSucc : Std.U8.wrapping_add count 1#u8 = countOut)
    (slotSucc : Std.Usize.wrapping_add slot 1#usize = slotOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk0 groupsAB
      (coefficientsAB a current) (countsAB 2#u8 count) slotsAB
      2#usize slot =
    ok (cont (groupsAB, coefficientsAB a output, countsAB 2#u8 countOut,
      slotsAB, 2#usize, slotOut)) := by
  apply aggregationExistingStep
    (basis := basis) (chunk := chunk0) (uniqueGroups := groupsAB)
    (coefficients := coefficientsAB a current)
    (coefficientsOut := coefficientsAB a output)
    (counts := countsAB 2#u8 count) (countsOut := countsAB 2#u8 countOut)
    (firstSlots := slotsAB) (uniqueLength := 2#usize)
    (position := 1#usize) (slot := slot) (slotOut := slotOut)
    (group := 1#u8) (count := count) (countOut := countOut)
    (coefficient := current) (basisValue := basisValue)
    (coefficientOut := output)
  · exact slotActive
  · exact groupRun
  · apply searchAt1 groupsAB 2#usize 1#u8 0#u8 (by decide) (by decide)
      groupsABIndex0 (by decide) groupsABIndex1
  · decide
  · exact coefficientsABIndex1 a current
  · exact basisRun
  · exact addRun
  · apply arrayUpdateTo (coefficientsAB a current)
      (coefficientsAB a output) 1#usize (by decide) output
    apply Subtype.ext; rfl
  · exact countsABIndex1 2#u8 count
  · exact countSucc
  · apply arrayUpdateTo (countsAB 2#u8 count) (countsAB 2#u8 countOut)
      1#usize (by decide) countOut
    apply Subtype.ext; rfl
  · exact slotSucc

structure Chunk0CoefficientTrace
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31) : Type where
  a0 : RawQM31
  c3 : RawQM31
  c4 : RawQM31
  c5 : RawQM31
  c6 : RawQM31
  c7 : RawQM31
  c8 : RawQM31
  c9 : RawQM31
  c10 : RawQM31
  c11 : RawQM31
  c12 : RawQM31
  c13 : RawQM31
  c14 : RawQM31
  c15 : RawQM31
  a0Run : field.QM31.add b0 b1 = ok a0
  c3Run : field.QM31.add b2 b3 = ok c3
  c4Run : field.QM31.add c3 b4 = ok c4
  c5Run : field.QM31.add c4 b5 = ok c5
  c6Run : field.QM31.add c5 b6 = ok c6
  c7Run : field.QM31.add c6 b7 = ok c7
  c8Run : field.QM31.add c7 b8 = ok c8
  c9Run : field.QM31.add c8 b9 = ok c9
  c10Run : field.QM31.add c9 b10 = ok c10
  c11Run : field.QM31.add c10 b11 = ok c11
  c12Run : field.QM31.add c11 b12 = ok c12
  c13Run : field.QM31.add c12 b13 = ok c13
  c14Run : field.QM31.add c13 b14 = ok c14
  c15Run : field.QM31.add c14 b15 = ok c15

private theorem repeatStep
    (basis : Array RawQM31 16#usize) (a current basisValue output : RawQM31)
    (count countOut : Std.U8) (slot slotOut : Std.Usize)
    (groupRun : Slice.index_usize chunk0 slot = ok 1#u8)
    (basisRun : Array.index_usize basis slot = ok basisValue)
    (addRun : field.QM31.add current basisValue = ok output)
    (countSucc : Std.U8.wrapping_add count 1#u8 = countOut)
    (slotSucc : Std.Usize.wrapping_add slot 1#usize = slotOut)
    (slotActive : slot < 16#usize) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk0 groupsAB
      (coefficientsAB a current) (countsAB 2#u8 count) slotsAB 2#usize slot =
    ok (cont (groupsAB, coefficientsAB a output, countsAB 2#u8 countOut,
      slotsAB, 2#usize, slotOut)) :=
  existingGroupBStep basis a current basisValue output count countOut slot
    slotOut slotActive groupRun basisRun addRun countSucc slotSucc

theorem chunk0_aggregation_exact
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31)
    (trace : Chunk0CoefficientTrace
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0
      (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
      chunk0 groups0 coefficients0 groups0 groups0 0#usize 0#usize =
    ok (groupsAB, coefficientsAB trace.a0 trace.c15,
      countsAB 2#u8 14#u8, slotsAB, 2#usize) := by
  let basis := basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  have groupRead (slot : Std.Usize) (bound : slot.val < 16)
      (valueExact : chunk0.val[slot.val]! = 1#u8) :
      Slice.index_usize chunk0 slot = ok 1#u8 :=
    chunk0IndexAt slot bound 1#u8 valueExact
  have basisRead (slot : Std.Usize) (bound : slot.val < 16)
      (value : RawQM31)
      (valueExact :
        ([b0, b1, b2, b3, b4, b5, b6, b7,
          b8, b9, b10, b11, b12, b13, b14, b15] : List RawQM31)[slot.val]! =
          value) : Array.index_usize basis slot = ok value := by
    simpa [basis] using basisIndexAt b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
      b11 b12 b13 b14 b15 slot bound value valueExact
  have usizeSucc (slot next : Std.Usize) (valueExact : slot.val + 1 = next.val) :
      Std.Usize.wrapping_add slot 1#usize = next :=
    usizeWrappingSuccExact slot next valueExact (by
      rw [valueExact]
      exact next.hSize)
  have u8Succ (count next : Std.U8) (valueExact : count.val + 1 = next.val) :
      Std.U8.wrapping_add count 1#u8 = next :=
    u8WrappingSuccExact count next valueExact (by
      rw [valueExact]
      exact next.hSize)
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0
  rw [loop.eq_1]
  dsimp only
  rw [step0 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step1 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
    trace.a0 trace.a0Run]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step2 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
    trace.a0]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 b2 b3 trace.c3 1#u8 2#u8 3#usize
    4#usize (groupRead 3#usize (by decide) rfl)
    (basisRead 3#usize (by decide) b3 rfl) trace.c3Run
    (u8Succ 1#u8 2#u8 rfl) (usizeSucc 3#usize 4#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 trace.c3 b4 trace.c4 2#u8 3#u8 4#usize
    5#usize (groupRead 4#usize (by decide) rfl)
    (basisRead 4#usize (by decide) b4 rfl) trace.c4Run
    (u8Succ 2#u8 3#u8 rfl) (usizeSucc 4#usize 5#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 trace.c4 b5 trace.c5 3#u8 4#u8 5#usize
    6#usize (groupRead 5#usize (by decide) rfl)
    (basisRead 5#usize (by decide) b5 rfl) trace.c5Run
    (u8Succ 3#u8 4#u8 rfl) (usizeSucc 5#usize 6#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 trace.c5 b6 trace.c6 4#u8 5#u8 6#usize
    7#usize (groupRead 6#usize (by decide) rfl)
    (basisRead 6#usize (by decide) b6 rfl) trace.c6Run
    (u8Succ 4#u8 5#u8 rfl) (usizeSucc 6#usize 7#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 trace.c6 b7 trace.c7 5#u8 6#u8 7#usize
    8#usize (groupRead 7#usize (by decide) rfl)
    (basisRead 7#usize (by decide) b7 rfl) trace.c7Run
    (u8Succ 5#u8 6#u8 rfl) (usizeSucc 7#usize 8#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 trace.c7 b8 trace.c8 6#u8 7#u8 8#usize
    9#usize (groupRead 8#usize (by decide) rfl)
    (basisRead 8#usize (by decide) b8 rfl) trace.c8Run
    (u8Succ 6#u8 7#u8 rfl) (usizeSucc 8#usize 9#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 trace.c8 b9 trace.c9 7#u8 8#u8 9#usize
    10#usize (groupRead 9#usize (by decide) rfl)
    (basisRead 9#usize (by decide) b9 rfl) trace.c9Run
    (u8Succ 7#u8 8#u8 rfl) (usizeSucc 9#usize 10#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 trace.c9 b10 trace.c10 8#u8 9#u8
    10#usize 11#usize (groupRead 10#usize (by decide) rfl)
    (basisRead 10#usize (by decide) b10 rfl) trace.c10Run
    (u8Succ 8#u8 9#u8 rfl) (usizeSucc 10#usize 11#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 trace.c10 b11 trace.c11 9#u8 10#u8
    11#usize 12#usize (groupRead 11#usize (by decide) rfl)
    (basisRead 11#usize (by decide) b11 rfl) trace.c11Run
    (u8Succ 9#u8 10#u8 rfl) (usizeSucc 11#usize 12#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 trace.c11 b12 trace.c12 10#u8 11#u8
    12#usize 13#usize (groupRead 12#usize (by decide) rfl)
    (basisRead 12#usize (by decide) b12 rfl) trace.c12Run
    (u8Succ 10#u8 11#u8 rfl) (usizeSucc 12#usize 13#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 trace.c12 b13 trace.c13 11#u8 12#u8
    13#usize 14#usize (groupRead 13#usize (by decide) rfl)
    (basisRead 13#usize (by decide) b13 rfl) trace.c13Run
    (u8Succ 11#u8 12#u8 rfl) (usizeSucc 13#usize 14#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 trace.c13 b14 trace.c14 12#u8 13#u8
    14#usize 15#usize (groupRead 14#usize (by decide) rfl)
    (basisRead 14#usize (by decide) b14 rfl) trace.c14Run
    (u8Succ 12#u8 13#u8 rfl) (usizeSucc 14#usize 15#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [repeatStep basis trace.a0 trace.c14 b15 trace.c15 13#u8 14#u8
    15#usize 16#usize (groupRead 15#usize (by decide) rfl)
    (basisRead 15#usize (by decide) b15 rfl) trace.c15Run
    (u8Succ 13#u8 14#u8 rfl) (usizeSucc 15#usize 16#usize rfl) (by decide)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [aggregationDone basis chunk0 groupsAB
    (coefficientsAB trace.a0 trace.c15) (countsAB 2#u8 14#u8)
    slotsAB 2#usize]

#print axioms step0
#print axioms step1
#print axioms step2
#print axioms chunk0_aggregation_exact

end V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0
