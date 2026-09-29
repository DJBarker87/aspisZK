import V7CallerCurrentReleaseR26GroupedRowsTwiceContributionStep

/-!
# Exact contribution loops for the four released chunks

The aggregation proofs determine a short list of unique groups for each
sixteen-row chunk.  This module replays the generated contribution loop over
those lists while keeping every field operation symbolic.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceContributions

open V7CallerCurrentReleaseR26GroupedRowsTwiceAggregationStep
open V7CallerCurrentReleaseR26GroupedRowsTwiceContributionStep

abbrev RawQM31 := field.QM31

private theorem arrayIndexAt
    {T : Type} [Inhabited T] (values : Array T 16#usize)
    (index : Std.Usize) (bound : index.val < 16) (value : T)
    (valueExact : values.val[index.val]! = value) :
    Array.index_usize values index = ok value := by
  rw [arrayIndexExact values index (by simpa using bound), valueExact]

private theorem castU8ToUsizeExact (value : Std.U8) (output : Std.Usize)
    (valueExact : value.val = output.val) :
    UScalar.cast .Usize value = output := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt]
  · exact valueExact
  · have h := value.hBounds
    rcases System.Platform.numBits_eq with hbits | hbits <;>
      norm_num [UScalarTy.numBits, hbits] at h ⊢ <;> omega

private theorem usizeSucc (value output : Std.Usize)
    (valueExact : value.val + 1 = output.val) :
    Std.Usize.wrapping_add value 1#usize = output :=
  usizeWrappingSuccExact value output valueExact (by
    rw [valueExact]
    exact output.hSize)

structure Chunk0ContributionTrace
    (groupValues : Slice RawQM31) (a0 a1 : RawQM31) : Type where
  value0 : RawQM31
  value1 : RawQM31
  product0 : RawQM31
  product1 : RawQM31
  sum0 : RawQM31
  sum1 : RawQM31
  value0Run : Slice.index_usize groupValues 0#usize = ok value0
  value1Run : Slice.index_usize groupValues 1#usize = ok value1
  product0Run : field.QM31.mul value0 a0 = ok product0
  product1Run : field.QM31.mul value1 a1 = ok product1
  sum0Run : field.QM31.add field.QM31.ZERO product0 = ok sum0
  sum1Run : field.QM31.add sum0 product1 = ok sum1

theorem chunk0_contribution_exact
    (groupValues : Slice RawQM31) (a0 a1 : RawQM31)
    (trace : Chunk0ContributionTrace groupValues a0 a1) :
    sumcheck.fold_grouped_rows_twice_loop0_loop1 groupValues
      V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.groupsAB
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.coefficientsAB a0 a1)
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.countsAB 2#u8 14#u8)
      V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.slotsAB
      2#usize field.QM31.ZERO 0#usize = ok trace.sum1 := by
  let groups := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.groupsAB
  let coefficients :=
    V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.coefficientsAB a0 a1
  let counts :=
    V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.countsAB 2#u8 14#u8
  let slots := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.slotsAB
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop1
  rw [loop.eq_1]
  dsimp only
  rw [contributionRepeatedZeroStep groupValues groups coefficients counts slots
    2#usize 0#usize 1#usize 0#u8 2#u8 0#usize field.QM31.ZERO
    trace.value0 a0 trace.product0 trace.sum0 (by decide)
    (arrayIndexAt groups 0#usize (by decide) 0#u8 rfl)
    (castU8ToUsizeExact 0#u8 0#usize rfl) trace.value0Run
    (arrayIndexAt slots 0#usize (by decide) 0#u8 rfl)
    (arrayIndexAt counts 0#usize (by decide) 2#u8 rfl) (by decide)
    (arrayIndexAt coefficients 0#usize (by decide) a0 rfl)
    trace.product0Run trace.sum0Run (usizeSucc 0#usize 1#usize rfl)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [contributionWeightedStep groupValues groups coefficients counts slots
    2#usize 1#usize 2#usize 1#u8 2#u8 1#usize trace.sum0
    trace.value1 a1 trace.product1 trace.sum1 (by decide)
    (arrayIndexAt groups 1#usize (by decide) 1#u8 rfl)
    (castU8ToUsizeExact 1#u8 1#usize rfl) trace.value1Run
    (arrayIndexAt slots 1#usize (by decide) 2#u8 rfl) (by decide)
    (arrayIndexAt coefficients 1#usize (by decide) a1 rfl)
    trace.product1Run trace.sum1Run (usizeSucc 1#usize 2#usize rfl)]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [contributionDone groupValues groups coefficients counts slots
    2#usize 2#usize trace.sum1 (by decide)]

structure Chunk1ContributionTrace
    (groupValues : Slice RawQM31) (a1 a2 : RawQM31) : Type where
  value1 : RawQM31
  value2 : RawQM31
  product1 : RawQM31
  product2 : RawQM31
  sum0 : RawQM31
  sum1 : RawQM31
  value1Run : Slice.index_usize groupValues 1#usize = ok value1
  value2Run : Slice.index_usize groupValues 2#usize = ok value2
  product1Run : field.QM31.mul value1 a1 = ok product1
  product2Run : field.QM31.mul value2 a2 = ok product2
  sum0Run : field.QM31.add field.QM31.ZERO product1 = ok sum0
  sum1Run : field.QM31.add sum0 product2 = ok sum1

theorem chunk1_contribution_exact
    (groupValues : Slice RawQM31) (a1 a2 : RawQM31)
    (trace : Chunk1ContributionTrace groupValues a1 a2) :
    sumcheck.fold_grouped_rows_twice_loop0_loop1 groupValues
      V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.uniqueAB
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.coefficients a1 a2)
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.counts 15#u8 1#u8)
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.firstSlots 0#u8 7#u8)
      2#usize field.QM31.ZERO 0#usize = ok trace.sum1 := by
  let groups := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.uniqueAB
  let coefficients := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.coefficients a1 a2
  let counts := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.counts 15#u8 1#u8
  let slots := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.firstSlots 0#u8 7#u8
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop1
  rw [loop.eq_1]; dsimp only
  rw [contributionRepeatedZeroStep groupValues groups coefficients counts slots
    2#usize 0#usize 1#usize 1#u8 15#u8 1#usize field.QM31.ZERO
    trace.value1 a1 trace.product1 trace.sum0 (by decide)
    (arrayIndexAt groups 0#usize (by decide) 1#u8 rfl)
    (castU8ToUsizeExact 1#u8 1#usize rfl) trace.value1Run
    (arrayIndexAt slots 0#usize (by decide) 0#u8 rfl)
    (arrayIndexAt counts 0#usize (by decide) 15#u8 rfl) (by decide)
    (arrayIndexAt coefficients 0#usize (by decide) a1 rfl)
    trace.product1Run trace.sum0Run (usizeSucc 0#usize 1#usize rfl)]
  simp only
  rw [loop.eq_1]; dsimp only
  rw [contributionWeightedStep groupValues groups coefficients counts slots
    2#usize 1#usize 2#usize 2#u8 7#u8 2#usize trace.sum0
    trace.value2 a2 trace.product2 trace.sum1 (by decide)
    (arrayIndexAt groups 1#usize (by decide) 2#u8 rfl)
    (castU8ToUsizeExact 2#u8 2#usize rfl) trace.value2Run
    (arrayIndexAt slots 1#usize (by decide) 7#u8 rfl) (by decide)
    (arrayIndexAt coefficients 1#usize (by decide) a2 rfl)
    trace.product2Run trace.sum1Run (usizeSucc 1#usize 2#usize rfl)]
  simp only
  rw [loop.eq_1]; dsimp only
  rw [contributionDone groupValues groups coefficients counts slots
    2#usize 2#usize trace.sum1 (by decide)]

structure Chunk2ContributionTrace
    (groupValues : Slice RawQM31) (a1 a2 a0 : RawQM31) : Type where
  value1 : RawQM31
  value2 : RawQM31
  value0 : RawQM31
  product1 : RawQM31
  product2 : RawQM31
  product0 : RawQM31
  sum0 : RawQM31
  sum1 : RawQM31
  sum2 : RawQM31
  value1Run : Slice.index_usize groupValues 1#usize = ok value1
  value2Run : Slice.index_usize groupValues 2#usize = ok value2
  value0Run : Slice.index_usize groupValues 0#usize = ok value0
  product1Run : field.QM31.mul value1 a1 = ok product1
  product2Run : field.QM31.mul value2 a2 = ok product2
  product0Run : field.QM31.mul value0 a0 = ok product0
  sum0Run : field.QM31.add field.QM31.ZERO product1 = ok sum0
  sum1Run : field.QM31.add sum0 product2 = ok sum1
  sum2Run : field.QM31.add sum1 product0 = ok sum2

theorem chunk2_contribution_exact
    (groupValues : Slice RawQM31) (a1 a2 a0 : RawQM31)
    (trace : Chunk2ContributionTrace groupValues a1 a2 a0) :
    sumcheck.fold_grouped_rows_twice_loop0_loop1 groupValues
      V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.uniqueABC
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.coefficients a1 a2 a0)
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.counts 12#u8 2#u8 2#u8)
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.firstSlots 0#u8 11#u8 12#u8)
      3#usize field.QM31.ZERO 0#usize = ok trace.sum2 := by
  let groups := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.uniqueABC
  let coefficients := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.coefficients a1 a2 a0
  let counts := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.counts 12#u8 2#u8 2#u8
  let slots := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.firstSlots 0#u8 11#u8 12#u8
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop1
  rw [loop.eq_1]; dsimp only
  rw [contributionRepeatedZeroStep groupValues groups coefficients counts slots
    3#usize 0#usize 1#usize 1#u8 12#u8 1#usize field.QM31.ZERO
    trace.value1 a1 trace.product1 trace.sum0 (by decide)
    (arrayIndexAt groups 0#usize (by decide) 1#u8 rfl)
    (castU8ToUsizeExact 1#u8 1#usize rfl) trace.value1Run
    (arrayIndexAt slots 0#usize (by decide) 0#u8 rfl)
    (arrayIndexAt counts 0#usize (by decide) 12#u8 rfl) (by decide)
    (arrayIndexAt coefficients 0#usize (by decide) a1 rfl)
    trace.product1Run trace.sum0Run (usizeSucc 0#usize 1#usize rfl)]
  simp only
  rw [loop.eq_1]; dsimp only
  rw [contributionWeightedStep groupValues groups coefficients counts slots
    3#usize 1#usize 2#usize 2#u8 11#u8 2#usize trace.sum0
    trace.value2 a2 trace.product2 trace.sum1 (by decide)
    (arrayIndexAt groups 1#usize (by decide) 2#u8 rfl)
    (castU8ToUsizeExact 2#u8 2#usize rfl) trace.value2Run
    (arrayIndexAt slots 1#usize (by decide) 11#u8 rfl) (by decide)
    (arrayIndexAt coefficients 1#usize (by decide) a2 rfl)
    trace.product2Run trace.sum1Run (usizeSucc 1#usize 2#usize rfl)]
  simp only
  rw [loop.eq_1]; dsimp only
  rw [contributionWeightedStep groupValues groups coefficients counts slots
    3#usize 2#usize 3#usize 0#u8 12#u8 0#usize trace.sum1
    trace.value0 a0 trace.product0 trace.sum2 (by decide)
    (arrayIndexAt groups 2#usize (by decide) 0#u8 rfl)
    (castU8ToUsizeExact 0#u8 0#usize rfl) trace.value0Run
    (arrayIndexAt slots 2#usize (by decide) 12#u8 rfl) (by decide)
    (arrayIndexAt coefficients 2#usize (by decide) a0 rfl)
    trace.product0Run trace.sum2Run (usizeSucc 2#usize 3#usize rfl)]
  simp only
  rw [loop.eq_1]; dsimp only
  rw [contributionDone groupValues groups coefficients counts slots
    3#usize 3#usize trace.sum2 (by decide)]

structure Chunk3ContributionTrace
    (groupValues : Slice RawQM31) (a1 a3 a4 a5 a6 : RawQM31) : Type where
  value1 : RawQM31
  value3 : RawQM31
  value4 : RawQM31
  value5 : RawQM31
  value6 : RawQM31
  product3 : RawQM31
  product4 : RawQM31
  product5 : RawQM31
  product6 : RawQM31
  sum0 : RawQM31
  sum1 : RawQM31
  sum2 : RawQM31
  sum3 : RawQM31
  sum4 : RawQM31
  value1Run : Slice.index_usize groupValues 1#usize = ok value1
  value3Run : Slice.index_usize groupValues 3#usize = ok value3
  value4Run : Slice.index_usize groupValues 4#usize = ok value4
  value5Run : Slice.index_usize groupValues 5#usize = ok value5
  value6Run : Slice.index_usize groupValues 6#usize = ok value6
  product3Run : field.QM31.mul value3 a3 = ok product3
  product4Run : field.QM31.mul value4 a4 = ok product4
  product5Run : field.QM31.mul value5 a5 = ok product5
  product6Run : field.QM31.mul value6 a6 = ok product6
  sum0Run : field.QM31.add field.QM31.ZERO value1 = ok sum0
  sum1Run : field.QM31.add sum0 product3 = ok sum1
  sum2Run : field.QM31.add sum1 product4 = ok sum2
  sum3Run : field.QM31.add sum2 product5 = ok sum3
  sum4Run : field.QM31.add sum3 product6 = ok sum4

theorem chunk3_contribution_exact
    (groupValues : Slice RawQM31) (a1 a3 a4 a5 a6 : RawQM31)
    (trace : Chunk3ContributionTrace groupValues a1 a3 a4 a5 a6) :
    sumcheck.fold_grouped_rows_twice_loop0_loop1 groupValues
      V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.unique13456
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.coefficients a1 a3 a4 a5 a6)
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.counts 1#u8 4#u8 1#u8 1#u8 9#u8)
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.firstSlots 0#u8 1#u8 5#u8 6#u8 7#u8)
      5#usize field.QM31.ZERO 0#usize = ok trace.sum4 := by
  let groups := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.unique13456
  let coefficients :=
    V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.coefficients a1 a3 a4 a5 a6
  let counts :=
    V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.counts 1#u8 4#u8 1#u8 1#u8 9#u8
  let slots :=
    V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.firstSlots 0#u8 1#u8 5#u8 6#u8 7#u8
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop1
  rw [loop.eq_1]; dsimp only
  rw [contributionSpecialStep groupValues groups coefficients counts slots
    5#usize 0#usize 1#usize 1#u8 1#usize field.QM31.ZERO trace.value1
    trace.sum0 (by decide) (arrayIndexAt groups 0#usize (by decide) 1#u8 rfl)
    (castU8ToUsizeExact 1#u8 1#usize rfl) trace.value1Run
    (arrayIndexAt slots 0#usize (by decide) 0#u8 rfl)
    (arrayIndexAt counts 0#usize (by decide) 1#u8 rfl)
    trace.sum0Run (usizeSucc 0#usize 1#usize rfl)]
  simp only
  rw [loop.eq_1]; dsimp only
  rw [contributionWeightedStep groupValues groups coefficients counts slots
    5#usize 1#usize 2#usize 3#u8 1#u8 3#usize trace.sum0
    trace.value3 a3 trace.product3 trace.sum1 (by decide)
    (arrayIndexAt groups 1#usize (by decide) 3#u8 rfl)
    (castU8ToUsizeExact 3#u8 3#usize rfl) trace.value3Run
    (arrayIndexAt slots 1#usize (by decide) 1#u8 rfl) (by decide)
    (arrayIndexAt coefficients 1#usize (by decide) a3 rfl)
    trace.product3Run trace.sum1Run (usizeSucc 1#usize 2#usize rfl)]
  simp only
  rw [loop.eq_1]; dsimp only
  rw [contributionWeightedStep groupValues groups coefficients counts slots
    5#usize 2#usize 3#usize 4#u8 5#u8 4#usize trace.sum1
    trace.value4 a4 trace.product4 trace.sum2 (by decide)
    (arrayIndexAt groups 2#usize (by decide) 4#u8 rfl)
    (castU8ToUsizeExact 4#u8 4#usize rfl) trace.value4Run
    (arrayIndexAt slots 2#usize (by decide) 5#u8 rfl) (by decide)
    (arrayIndexAt coefficients 2#usize (by decide) a4 rfl)
    trace.product4Run trace.sum2Run (usizeSucc 2#usize 3#usize rfl)]
  simp only
  rw [loop.eq_1]; dsimp only
  rw [contributionWeightedStep groupValues groups coefficients counts slots
    5#usize 3#usize 4#usize 5#u8 6#u8 5#usize trace.sum2
    trace.value5 a5 trace.product5 trace.sum3 (by decide)
    (arrayIndexAt groups 3#usize (by decide) 5#u8 rfl)
    (castU8ToUsizeExact 5#u8 5#usize rfl) trace.value5Run
    (arrayIndexAt slots 3#usize (by decide) 6#u8 rfl) (by decide)
    (arrayIndexAt coefficients 3#usize (by decide) a5 rfl)
    trace.product5Run trace.sum3Run (usizeSucc 3#usize 4#usize rfl)]
  simp only
  rw [loop.eq_1]; dsimp only
  rw [contributionWeightedStep groupValues groups coefficients counts slots
    5#usize 4#usize 5#usize 6#u8 7#u8 6#usize trace.sum3
    trace.value6 a6 trace.product6 trace.sum4 (by decide)
    (arrayIndexAt groups 4#usize (by decide) 6#u8 rfl)
    (castU8ToUsizeExact 6#u8 6#usize rfl) trace.value6Run
    (arrayIndexAt slots 4#usize (by decide) 7#u8 rfl) (by decide)
    (arrayIndexAt coefficients 4#usize (by decide) a6 rfl)
    trace.product6Run trace.sum4Run (usizeSucc 4#usize 5#usize rfl)]
  simp only
  rw [loop.eq_1]; dsimp only
  rw [contributionDone groupValues groups coefficients counts slots
    5#usize 5#usize trace.sum4 (by decide)]

#print axioms chunk0_contribution_exact
#print axioms chunk1_contribution_exact
#print axioms chunk2_contribution_exact
#print axioms chunk3_contribution_exact

end V7CallerCurrentReleaseR26GroupedRowsTwiceContributions
