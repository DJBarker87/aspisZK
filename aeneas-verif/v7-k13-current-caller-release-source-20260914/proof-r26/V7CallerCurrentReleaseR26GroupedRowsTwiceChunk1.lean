import V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0

/-!
# Source-exact aggregation for released chunk one

Chunk one contains group one in every slot except slot seven, which contains
group two.  This proof keeps the generated loop symbolic by replaying sixteen
named aggregation transitions.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1

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

def coefficients (a b : RawQM31) : Array RawQM31 16#usize :=
  Array.make 16#usize
    [a, b, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO,
     field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO]
def counts (a b : Std.U8) : Array Std.U8 16#usize :=
  Array.make 16#usize
    [a, b, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
     0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
def firstSlots (a b : Std.U8) : Array Std.U8 16#usize :=
  Array.make 16#usize
    [a, b, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
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

private theorem chunk1IndexAt
    (index : Std.Usize) (bound : index.val < 16) (value : Std.U8)
    (valueExact : chunk1.val[index.val]! = value) :
    Slice.index_usize chunk1 index = ok value := by
  have run := sliceIndexExact chunk1 index (by simpa [chunk1] using bound)
  rwa [valueExact] at run

private theorem step0
    (basis : Array RawQM31 16#usize) (b0 : RawQM31)
    (basisRun : Array.index_usize basis 0#usize = ok b0) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk1 groups0
      coefficients0 groups0 groups0 0#usize 0#usize =
    ok (cont (uniqueA, coefficients b0 field.QM31.ZERO,
      counts 1#u8 0#u8, firstSlots 0#u8 0#u8, 1#usize, 1#usize)) := by
  apply aggregationNewStep
    (basis := basis) (chunk := chunk1) (uniqueGroups := groups0)
    (uniqueGroupsOut := uniqueA) (coefficients := coefficients0)
    (coefficientsOut := coefficients b0 field.QM31.ZERO) (counts := groups0)
    (countsOut := counts 1#u8 0#u8) (firstSlots := groups0)
    (firstSlotsOut := firstSlots 0#u8 0#u8) (uniqueLength := 0#usize)
    (uniqueLengthOut := 1#usize) (slot := 0#usize) (slotOut := 1#usize)
    (group := 1#u8) (slotU8 := 0#u8) (coefficient := b0)
  · decide
  · exact chunk1IndexAt 0#usize (by decide) 1#u8 rfl
  · exact searchEmpty groups0 1#u8
  · apply arrayUpdateTo groups0 uniqueA 0#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact basisRun
  · apply arrayUpdateTo coefficients0 (coefficients b0 field.QM31.ZERO)
      0#usize (by decide) b0
    apply Subtype.ext; rfl
  · apply arrayUpdateTo groups0 (counts 1#u8 0#u8) 0#usize
      (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact castUsizeToU8Exact 0#usize 0#u8 rfl (by decide)
  · apply arrayUpdateTo groups0 (firstSlots 0#u8 0#u8) 0#usize
      (by decide) 0#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 0#usize 1#usize rfl (by
      have h := (1#usize).hSize; scalar_tac)
  · exact usizeWrappingSuccExact 0#usize 1#usize rfl (by
      have h := (1#usize).hSize; scalar_tac)

private theorem existingAt0
    (basis : Array RawQM31 16#usize)
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength : Std.Usize)
    (otherCoefficient : RawQM31) (otherCount otherSlot : Std.U8)
    (current basisValue output : RawQM31) (count countOut : Std.U8)
    (slot slotOut : Std.Usize) (uniqueActive : 0#usize < uniqueLength)
    (uniqueRead : Array.index_usize uniqueGroups 0#usize = ok 1#u8)
    (slotActive : slot < 16#usize)
    (groupRun : Slice.index_usize chunk1 slot = ok 1#u8)
    (basisRun : Array.index_usize basis slot = ok basisValue)
    (addRun : field.QM31.add current basisValue = ok output)
    (countSucc : Std.U8.wrapping_add count 1#u8 = countOut)
    (slotSucc : Std.Usize.wrapping_add slot 1#usize = slotOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk1 uniqueGroups
      (coefficients current otherCoefficient) (counts count otherCount)
      (firstSlots 0#u8 otherSlot) uniqueLength slot =
    ok (cont (uniqueGroups, coefficients output otherCoefficient,
      counts countOut otherCount, firstSlots 0#u8 otherSlot,
      uniqueLength, slotOut)) := by
  apply aggregationExistingStep
    (basis := basis) (chunk := chunk1) (uniqueGroups := uniqueGroups)
    (coefficients := coefficients current otherCoefficient)
    (coefficientsOut := coefficients output otherCoefficient)
    (counts := counts count otherCount) (countsOut := counts countOut otherCount)
    (firstSlots := firstSlots 0#u8 otherSlot) (uniqueLength := uniqueLength)
    (position := 0#usize) (slot := slot) (slotOut := slotOut)
    (group := 1#u8) (count := count) (countOut := countOut)
    (coefficient := current) (basisValue := basisValue)
    (coefficientOut := output)
  · exact slotActive
  · exact groupRun
  · exact searchAt0 uniqueGroups uniqueLength 1#u8 uniqueActive uniqueRead
  · intro same
    have := congrArg UScalar.val same
    scalar_tac
  · exact arrayIndexAt (coefficients current otherCoefficient) 0#usize
      (by decide) current rfl
  · exact basisRun
  · exact addRun
  · apply arrayUpdateTo (coefficients current otherCoefficient)
      (coefficients output otherCoefficient) 0#usize (by decide) output
    apply Subtype.ext; rfl
  · exact arrayIndexAt (counts count otherCount) 0#usize
      (by decide) count rfl
  · exact countSucc
  · apply arrayUpdateTo (counts count otherCount) (counts countOut otherCount)
      0#usize (by decide) countOut
    apply Subtype.ext; rfl
  · exact slotSucc

private theorem newGroup2
    (basis : Array RawQM31 16#usize) (current b7 : RawQM31)
    (basisRun : Array.index_usize basis 7#usize = ok b7) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk1 uniqueA
      (coefficients current field.QM31.ZERO) (counts 7#u8 0#u8)
      (firstSlots 0#u8 0#u8) 1#usize 7#usize =
    ok (cont (uniqueAB, coefficients current b7, counts 7#u8 1#u8,
      firstSlots 0#u8 7#u8, 2#usize, 8#usize)) := by
  apply aggregationNewStep
    (basis := basis) (chunk := chunk1) (uniqueGroups := uniqueA)
    (uniqueGroupsOut := uniqueAB)
    (coefficients := coefficients current field.QM31.ZERO)
    (coefficientsOut := coefficients current b7) (counts := counts 7#u8 0#u8)
    (countsOut := counts 7#u8 1#u8) (firstSlots := firstSlots 0#u8 0#u8)
    (firstSlotsOut := firstSlots 0#u8 7#u8) (uniqueLength := 1#usize)
    (uniqueLengthOut := 2#usize) (slot := 7#usize) (slotOut := 8#usize)
    (group := 2#u8) (slotU8 := 7#u8) (coefficient := b7)
  · decide
  · exact chunk1IndexAt 7#usize (by decide) 2#u8 rfl
  · apply searchNew1 uniqueA 2#u8 1#u8
    · exact arrayIndexAt uniqueA 0#usize (by decide) 1#u8 rfl
    · decide
  · apply arrayUpdateTo uniqueA uniqueAB 1#usize (by decide) 2#u8
    apply Subtype.ext; rfl
  · exact basisRun
  · apply arrayUpdateTo (coefficients current field.QM31.ZERO)
      (coefficients current b7) 1#usize (by decide) b7
    apply Subtype.ext; rfl
  · apply arrayUpdateTo (counts 7#u8 0#u8) (counts 7#u8 1#u8)
      1#usize (by decide) 1#u8
    apply Subtype.ext; rfl
  · exact castUsizeToU8Exact 7#usize 7#u8 rfl (by decide)
  · apply arrayUpdateTo (firstSlots 0#u8 0#u8)
      (firstSlots 0#u8 7#u8) 1#usize (by decide) 7#u8
    apply Subtype.ext; rfl
  · exact usizeWrappingSuccExact 1#usize 2#usize rfl (by
      have h := (2#usize).hSize; scalar_tac)
  · exact usizeWrappingSuccExact 7#usize 8#usize rfl (by
      have h := (8#usize).hSize; scalar_tac)

structure Chunk1CoefficientTrace
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31) : Type where
  c1 : RawQM31
  c2 : RawQM31
  c3 : RawQM31
  c4 : RawQM31
  c5 : RawQM31
  c6 : RawQM31
  c8 : RawQM31
  c9 : RawQM31
  c10 : RawQM31
  c11 : RawQM31
  c12 : RawQM31
  c13 : RawQM31
  c14 : RawQM31
  c15 : RawQM31
  c1Run : field.QM31.add b0 b1 = ok c1
  c2Run : field.QM31.add c1 b2 = ok c2
  c3Run : field.QM31.add c2 b3 = ok c3
  c4Run : field.QM31.add c3 b4 = ok c4
  c5Run : field.QM31.add c4 b5 = ok c5
  c6Run : field.QM31.add c5 b6 = ok c6
  c8Run : field.QM31.add c6 b8 = ok c8
  c9Run : field.QM31.add c8 b9 = ok c9
  c10Run : field.QM31.add c9 b10 = ok c10
  c11Run : field.QM31.add c10 b11 = ok c11
  c12Run : field.QM31.add c11 b12 = ok c12
  c13Run : field.QM31.add c12 b13 = ok c13
  c14Run : field.QM31.add c13 b14 = ok c14
  c15Run : field.QM31.add c14 b15 = ok c15

theorem chunk1_aggregation_exact
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
      RawQM31)
    (trace : Chunk1CoefficientTrace
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0
      (basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
      chunk1 groups0 coefficients0 groups0 groups0 0#usize 0#usize =
    ok (uniqueAB, coefficients trace.c15 b7, counts 15#u8 1#u8,
      firstSlots 0#u8 7#u8, 2#usize) := by
  let basis := basis16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  have basisRead (slot : Std.Usize) (bound : slot.val < 16)
      (value : RawQM31)
      (valueExact :
        ([b0, b1, b2, b3, b4, b5, b6, b7,
          b8, b9, b10, b11, b12, b13, b14, b15] : List RawQM31)[slot.val]! =
          value) : Array.index_usize basis slot = ok value := by
    simpa [basis] using basisIndexAt b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
      b11 b12 b13 b14 b15 slot bound value valueExact
  have groupRead (slot : Std.Usize) (bound : slot.val < 16)
      (valueExact : chunk1.val[slot.val]! = 1#u8) :
      Slice.index_usize chunk1 slot = ok 1#u8 :=
    chunk1IndexAt slot bound 1#u8 valueExact
  have usizeSucc (slot next : Std.Usize) (valueExact : slot.val + 1 = next.val) :
      Std.Usize.wrapping_add slot 1#usize = next :=
    usizeWrappingSuccExact slot next valueExact (by rw [valueExact]; exact next.hSize)
  have u8Succ (count next : Std.U8) (valueExact : count.val + 1 = next.val) :
      Std.U8.wrapping_add count 1#u8 = next :=
    u8WrappingSuccExact count next valueExact (by rw [valueExact]; exact next.hSize)
  have readA : Array.index_usize uniqueA 0#usize = ok 1#u8 :=
    arrayIndexAt uniqueA 0#usize (by decide) 1#u8 rfl
  have readAB : Array.index_usize uniqueAB 0#usize = ok 1#u8 :=
    arrayIndexAt uniqueAB 0#usize (by decide) 1#u8 rfl
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0
  rw [loop.eq_1]; dsimp only
  rw [step0 basis b0 (basisRead 0#usize (by decide) b0 rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize field.QM31.ZERO 0#u8 0#u8
    b0 b1 trace.c1 1#u8 2#u8 1#usize 2#usize (by decide) readA (by decide)
    (groupRead 1#usize (by decide) rfl) (basisRead 1#usize (by decide) b1 rfl)
    trace.c1Run (u8Succ 1#u8 2#u8 rfl) (usizeSucc 1#usize 2#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize field.QM31.ZERO 0#u8 0#u8
    trace.c1 b2 trace.c2 2#u8 3#u8 2#usize 3#usize (by decide) readA (by decide)
    (groupRead 2#usize (by decide) rfl) (basisRead 2#usize (by decide) b2 rfl)
    trace.c2Run (u8Succ 2#u8 3#u8 rfl) (usizeSucc 2#usize 3#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize field.QM31.ZERO 0#u8 0#u8
    trace.c2 b3 trace.c3 3#u8 4#u8 3#usize 4#usize (by decide) readA (by decide)
    (groupRead 3#usize (by decide) rfl) (basisRead 3#usize (by decide) b3 rfl)
    trace.c3Run (u8Succ 3#u8 4#u8 rfl) (usizeSucc 3#usize 4#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize field.QM31.ZERO 0#u8 0#u8
    trace.c3 b4 trace.c4 4#u8 5#u8 4#usize 5#usize (by decide) readA (by decide)
    (groupRead 4#usize (by decide) rfl) (basisRead 4#usize (by decide) b4 rfl)
    trace.c4Run (u8Succ 4#u8 5#u8 rfl) (usizeSucc 4#usize 5#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize field.QM31.ZERO 0#u8 0#u8
    trace.c4 b5 trace.c5 5#u8 6#u8 5#usize 6#usize (by decide) readA (by decide)
    (groupRead 5#usize (by decide) rfl) (basisRead 5#usize (by decide) b5 rfl)
    trace.c5Run (u8Succ 5#u8 6#u8 rfl) (usizeSucc 5#usize 6#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueA 1#usize field.QM31.ZERO 0#u8 0#u8
    trace.c5 b6 trace.c6 6#u8 7#u8 6#usize 7#usize (by decide) readA (by decide)
    (groupRead 6#usize (by decide) rfl) (basisRead 6#usize (by decide) b6 rfl)
    trace.c6Run (u8Succ 6#u8 7#u8 rfl) (usizeSucc 6#usize 7#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [newGroup2 basis trace.c6 b7 (basisRead 7#usize (by decide) b7 rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueAB 2#usize b7 1#u8 7#u8
    trace.c6 b8 trace.c8 7#u8 8#u8 8#usize 9#usize (by decide) readAB (by decide)
    (groupRead 8#usize (by decide) rfl) (basisRead 8#usize (by decide) b8 rfl)
    trace.c8Run (u8Succ 7#u8 8#u8 rfl) (usizeSucc 8#usize 9#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueAB 2#usize b7 1#u8 7#u8
    trace.c8 b9 trace.c9 8#u8 9#u8 9#usize 10#usize (by decide) readAB (by decide)
    (groupRead 9#usize (by decide) rfl) (basisRead 9#usize (by decide) b9 rfl)
    trace.c9Run (u8Succ 8#u8 9#u8 rfl) (usizeSucc 9#usize 10#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueAB 2#usize b7 1#u8 7#u8
    trace.c9 b10 trace.c10 9#u8 10#u8 10#usize 11#usize (by decide) readAB (by decide)
    (groupRead 10#usize (by decide) rfl) (basisRead 10#usize (by decide) b10 rfl)
    trace.c10Run (u8Succ 9#u8 10#u8 rfl) (usizeSucc 10#usize 11#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueAB 2#usize b7 1#u8 7#u8
    trace.c10 b11 trace.c11 10#u8 11#u8 11#usize 12#usize (by decide) readAB (by decide)
    (groupRead 11#usize (by decide) rfl) (basisRead 11#usize (by decide) b11 rfl)
    trace.c11Run (u8Succ 10#u8 11#u8 rfl) (usizeSucc 11#usize 12#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueAB 2#usize b7 1#u8 7#u8
    trace.c11 b12 trace.c12 11#u8 12#u8 12#usize 13#usize (by decide) readAB (by decide)
    (groupRead 12#usize (by decide) rfl) (basisRead 12#usize (by decide) b12 rfl)
    trace.c12Run (u8Succ 11#u8 12#u8 rfl) (usizeSucc 12#usize 13#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueAB 2#usize b7 1#u8 7#u8
    trace.c12 b13 trace.c13 12#u8 13#u8 13#usize 14#usize (by decide) readAB (by decide)
    (groupRead 13#usize (by decide) rfl) (basisRead 13#usize (by decide) b13 rfl)
    trace.c13Run (u8Succ 12#u8 13#u8 rfl) (usizeSucc 13#usize 14#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueAB 2#usize b7 1#u8 7#u8
    trace.c13 b14 trace.c14 13#u8 14#u8 14#usize 15#usize (by decide) readAB (by decide)
    (groupRead 14#usize (by decide) rfl) (basisRead 14#usize (by decide) b14 rfl)
    trace.c14Run (u8Succ 13#u8 14#u8 rfl) (usizeSucc 14#usize 15#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [existingAt0 basis uniqueAB 2#usize b7 1#u8 7#u8
    trace.c14 b15 trace.c15 14#u8 15#u8 15#usize 16#usize (by decide) readAB (by decide)
    (groupRead 15#usize (by decide) rfl) (basisRead 15#usize (by decide) b15 rfl)
    trace.c15Run (u8Succ 14#u8 15#u8 rfl) (usizeSucc 15#usize 16#usize rfl)]; simp only
  rw [loop.eq_1]; dsimp only
  rw [aggregationDone basis chunk1 uniqueAB (coefficients trace.c15 b7)
    (counts 15#u8 1#u8) (firstSlots 0#u8 7#u8) 2#usize]

#print axioms chunk1_aggregation_exact

end V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1
