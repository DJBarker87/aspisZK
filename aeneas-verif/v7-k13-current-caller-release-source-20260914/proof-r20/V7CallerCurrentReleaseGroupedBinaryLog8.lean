import V7CallerCurrentReleaseHalfBridge

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7CallerCurrentReleaseGroupedBinaryLog8

open V7CallerCurrentReleaseFieldBridge
open V7CallerCurrentReleaseHalfBridge

abbrev M31 := V7CallerCurrentReleaseR20.field.M31
abbrev QM31 := V7CallerCurrentReleaseR20.field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseFieldBridge.ExactQM31

def Canonical (x : QM31) : Prop := GeneratedCanonicalQM31 x

def selectedNibble (mask : Std.U16) (shift : Nat) : Nat :=
  (mask.val / 2 ^ shift) % 16

def nibbleSum (alpha : ExactQM31) (bits : Nat) : ExactQM31 :=
  (if bits % 2 = 1 then 1 else 0) +
    (if (bits / 2) % 2 = 1 then alpha ^ 3 else 0) +
    (if (bits / 4) % 2 = 1 then alpha ^ 2 else 0) +
    (if (bits / 8) % 2 = 1 then alpha else 0)

def rawNibbleSum (alpha : ExactQM31) (bits : Std.U16) : ExactQM31 :=
  (if bits &&& 1#u16 != 0#u16 then 1 else 0) +
    (if bits &&& 2#u16 != 0#u16 then alpha ^ 3 else 0) +
    (if bits &&& 4#u16 != 0#u16 then alpha ^ 2 else 0) +
    (if bits &&& 8#u16 != 0#u16 then alpha else 0)

def groupedArithmetic (alpha : QM31) (bits : Std.U16) : Result QM31 := do
  let alpha2 ← V7CallerCurrentReleaseR20.field.QM31.square alpha
  let alpha3 ← V7CallerCurrentReleaseR20.field.QM31.mul alpha2 alpha
  let sum ← if bits &&& 1#u16 != 0#u16 then
      V7CallerCurrentReleaseR20.field.QM31.add V7CallerCurrentReleaseR20.field.QM31.ZERO
        V7CallerCurrentReleaseR20.field.QM31.ONE
    else ok V7CallerCurrentReleaseR20.field.QM31.ZERO
  let sum1 ← if bits &&& 2#u16 != 0#u16 then
      V7CallerCurrentReleaseR20.field.QM31.add sum alpha3 else ok sum
  let sum2 ← if bits &&& 4#u16 != 0#u16 then
      V7CallerCurrentReleaseR20.field.QM31.add sum1 alpha2 else ok sum1
  let sum3 ← if bits &&& 8#u16 != 0#u16 then
      V7CallerCurrentReleaseR20.field.QM31.add sum2 alpha else ok sum2
  let half ← V7CallerCurrentReleaseR20.field.QM31.half sum3
  V7CallerCurrentReleaseR20.field.QM31.half half

def sourceBits (mask : Std.U16) (index : Std.U32) : Std.U16 :=
  let indexUsize := UScalar.cast .Usize index
  let lowChunk := indexUsize &&& 3#usize
  let shift := UScalar.cast .U32 (Std.Usize.wrapping_mul 4#usize lowChunk)
  Std.U16.wrapping_shr mask shift &&& 15#u16

private theorem generated_arithmetic_eq_grouped
    (alpha : QM31) (bits : Std.U16) :
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_grouped_binary_deferred_log8_arithmetic
        alpha bits = groupedArithmetic alpha bits := by
  rfl

private theorem generated_zero_canonical :
    GeneratedCanonicalQM31 V7CallerCurrentReleaseR20.field.QM31.ZERO := by
  norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V7CallerCurrentReleaseR20.field.QM31.ZERO]

private theorem generated_one_canonical :
    GeneratedCanonicalQM31 V7CallerCurrentReleaseR20.field.QM31.ONE := by
  norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V7CallerCurrentReleaseR20.field.QM31.ONE]

private theorem generated_zero_exact :
    generatedQm31ToExact V7CallerCurrentReleaseR20.field.QM31.ZERO = 0 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [generatedQm31ToExact, generatedCm31ToExact,
        V7CallerCurrentReleaseR20.field.QM31.ZERO]
  · apply QuadraticAlgebra.ext <;>
      simp [generatedQm31ToExact, generatedCm31ToExact,
        V7CallerCurrentReleaseR20.field.QM31.ZERO]

private theorem generated_one_exact :
    generatedQm31ToExact V7CallerCurrentReleaseR20.field.QM31.ONE = 1 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [generatedQm31ToExact, generatedCm31ToExact,
        V7CallerCurrentReleaseR20.field.QM31.ONE, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one]
  · apply QuadraticAlgebra.ext <;>
      simp [generatedQm31ToExact, generatedCm31ToExact,
        V7CallerCurrentReleaseR20.field.QM31.ONE, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one]

private theorem optional_add_corresponds
    (current term : QM31) (condition : Prop) [Decidable condition]
    (hCurrent : GeneratedCanonicalQM31 current)
    (hTerm : GeneratedCanonicalQM31 term) :
    ∃ out,
      (if condition then V7CallerCurrentReleaseR20.field.QM31.add current term
        else ok current) = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = generatedQm31ToExact current +
        (if condition then generatedQm31ToExact term else 0) := by
  by_cases h : condition
  · obtain ⟨out, hrun, hcanonical, hexact⟩ :=
      generated_qm31_add_corresponds current term hCurrent hTerm
    exact ⟨out, by simpa [h] using hrun, hcanonical, by simpa [h] using hexact⟩
  · exact ⟨current, by simp [h], hCurrent, by simp [h]⟩

private theorem slice_index_run
    {T : Type} [Inhabited T] (values : Slice T) (index : Std.Usize)
    (hIndex : index.val < values.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, hRun, hValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.index_usize_spec values index (by simpa using hIndex))
  have hList : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using hIndex
  simpa [hValue, hList] using hRun

private theorem cast_u32_usize_val (value : Std.U32) :
    (UScalar.cast .Usize value).val = value.val := by
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
  rw [UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> rw [h]
  · exact value.bv.isLt
  · exact lt_trans value.bv.isLt (by norm_num)

private theorem usize_div_four_run (value : Std.Usize) :
    ∃ quotient,
      value / 4#usize = ok quotient ∧ quotient.val = value.val / 4 := by
  obtain ⟨quotient, hrun, hval⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.div_spec value (y := 4#usize) (by norm_num))
  exact ⟨quotient, hrun, by simpa using hval⟩

private theorem index_div4_bound {index : Std.U32} (hIndex : index.val < 256) :
    index.val / 4 < 64 := by omega

private theorem index_mod4_bound {index : Std.U32} (hIndex : index.val < 256) :
    index.val % 4 < 4 := by omega

private theorem source_shift_bound {index : Std.U32} (hIndex : index.val < 256) :
    4 * (index.val % 4) < 16 := by omega

/-- The source-authentic log-eight deferred binary evaluator uses the four
    nibble bits with powers `[1, alpha^3, alpha^2, alpha]`, then applies the
    two source halving operations.  This is restricted to the live shape:
    64 row groups, 64 masks, and a 256-entry index domain. -/
theorem selected_nibble_lt16 (mask : Std.U16) (shift : Nat) :
    selectedNibble mask shift < 16 := by
  unfold selectedNibble
  omega

theorem live_index_bounds {index : Std.U32} (hIndex : index.val < 256) :
    index.val / 4 < 64 ∧ index.val % 4 < 4 ∧ 4 * (index.val % 4) < 16 := by
  omega

/-- The four source tests are exactly the four binary digits of the selected
    low nibble.  This is the finite bit-selection fact consumed by the
    source-authentic log-eight evaluator. -/
theorem nibble_sum_bit_expansion
    (alpha : ExactQM31) (bits : Nat) (hbits : bits < 16) :
    nibbleSum alpha bits =
      (if bits % 2 = 1 then 1 else 0) +
      (if (bits / 2) % 2 = 1 then alpha ^ 3 else 0) +
      (if (bits / 4) % 2 = 1 then alpha ^ 2 else 0) +
      (if (bits / 8) % 2 = 1 then alpha else 0) := by
  rfl

theorem generated_grouped_arithmetic_corresponds
    (alpha : QM31) (bits : Std.U16)
    (hAlpha : GeneratedCanonicalQM31 alpha) :
    ∃ out,
      groupedArithmetic alpha bits = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out + generatedQm31ToExact out +
          generatedQm31ToExact out + generatedQm31ToExact out =
        rawNibbleSum (generatedQm31ToExact alpha) bits := by
  obtain ⟨alpha2, hAlpha2, hAlpha2Canonical, hAlpha2Exact⟩ :=
    generated_qm31_square_corresponds alpha hAlpha
  obtain ⟨alpha3, hAlpha3, hAlpha3Canonical, hAlpha3Exact⟩ :=
    generated_qm31_mul_corresponds alpha2 alpha hAlpha2Canonical hAlpha
  obtain ⟨sum0, hSum0, hSum0Canonical, hSum0Exact⟩ :=
    optional_add_corresponds V7CallerCurrentReleaseR20.field.QM31.ZERO
      V7CallerCurrentReleaseR20.field.QM31.ONE (bits &&& 1#u16 != 0#u16)
      generated_zero_canonical generated_one_canonical
  obtain ⟨sum1, hSum1, hSum1Canonical, hSum1Exact⟩ :=
    optional_add_corresponds sum0 alpha3 (bits &&& 2#u16 != 0#u16)
      hSum0Canonical hAlpha3Canonical
  obtain ⟨sum2, hSum2, hSum2Canonical, hSum2Exact⟩ :=
    optional_add_corresponds sum1 alpha2 (bits &&& 4#u16 != 0#u16)
      hSum1Canonical hAlpha2Canonical
  obtain ⟨sum3, hSum3, hSum3Canonical, hSum3Exact⟩ :=
    optional_add_corresponds sum2 alpha (bits &&& 8#u16 != 0#u16)
      hSum2Canonical hAlpha
  obtain ⟨half1, hHalf1, hHalf1Canonical, hHalf1Equation⟩ :=
    generated_qm31_half_corresponds sum3 hSum3Canonical
  obtain ⟨half2, hHalf2, hHalf2Canonical, hHalf2Equation⟩ :=
    generated_qm31_half_corresponds half1 hHalf1Canonical
  refine ⟨half2, ?_, hHalf2Canonical, ?_⟩
  · by_cases b0 : bits &&& 1#u16 != 0#u16
    <;> by_cases b1 : bits &&& 2#u16 != 0#u16
    <;> by_cases b2 : bits &&& 4#u16 != 0#u16
    <;> by_cases b3 : bits &&& 8#u16 != 0#u16
    <;> simp_all [groupedArithmetic]
  · have hFour :
        generatedQm31ToExact half2 + generatedQm31ToExact half2 +
            generatedQm31ToExact half2 + generatedQm31ToExact half2 =
          generatedQm31ToExact sum3 := by
      calc
        _ = (generatedQm31ToExact half2 + generatedQm31ToExact half2) +
              (generatedQm31ToExact half2 + generatedQm31ToExact half2) := by ring
        _ = generatedQm31ToExact half1 + generatedQm31ToExact half1 := by
          rw [hHalf2Equation]
        _ = generatedQm31ToExact sum3 := hHalf1Equation
    rw [hFour, hSum3Exact, hSum2Exact, hSum1Exact, hSum0Exact,
      hAlpha3Exact, hAlpha2Exact, generated_zero_exact, generated_one_exact]
    unfold rawNibbleSum
    ring

set_option maxHeartbeats 2000000 in
theorem generated_grouped_log8_corresponds
    (rowGroups : Slice Std.U8) (groupMasks : Slice Std.U16)
    (alpha : QM31) (index : Std.U32)
    (hIndex : index.val < 256)
    (hRows : rowGroups.length = 64)
    (hGroup : ∀ row, row < 64 → rowGroups.val[row]!.val < groupMasks.length)
    (hAlpha : GeneratedCanonicalQM31 alpha) :
    ∃ out,
      V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_grouped_binary_deferred_log8
          rowGroups groupMasks (some alpha) index = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out + generatedQm31ToExact out +
          generatedQm31ToExact out + generatedQm31ToExact out =
        rawNibbleSum (generatedQm31ToExact alpha)
          (sourceBits groupMasks.val[rowGroups.val[index.val / 4]!.val]! index) := by
  let indexUsize := UScalar.cast .Usize index
  have hIndexUsize : indexUsize.val = index.val := cast_u32_usize_val index
  obtain ⟨high, hHighRun, hHighVal⟩ := usize_div_four_run indexUsize
  have hHighBound : high.val < rowGroups.length := by
    rw [hHighVal, hIndexUsize, hRows]
    omega
  let row := rowGroups.val[index.val / 4]!
  have hRowRun : Slice.index_usize rowGroups high = ok row := by
    have h := slice_index_run rowGroups high hHighBound
    simpa [row, hHighVal, hIndexUsize] using h
  let group := core.convert.num.FromUsizeU8.from row
  have hGroupVal : group.val = row.val := by
    dsimp only [group]
    unfold core.convert.num.FromUsizeU8.from UScalar.val
    change (BitVec.setWidth UScalarTy.Usize.numBits row.bv).toNat = row.bv.toNat
    rw [BitVec.toNat_setWidth]
    apply Nat.mod_eq_of_lt
    rw [UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;> rw [h]
    · exact lt_trans row.bv.isLt (by norm_num)
    · exact lt_trans row.bv.isLt (by norm_num)
  have hGroupBound : group.val < groupMasks.length := by
    rw [hGroupVal]
    apply hGroup (index.val / 4)
    omega
  let mask := groupMasks.val[row.val]!
  have hMaskRun : Slice.index_usize groupMasks group = ok mask := by
    have h := slice_index_run groupMasks group hGroupBound
    simpa [mask, hGroupVal] using h
  obtain ⟨out, hArithmetic, hOutCanonical, hOutExact⟩ :=
    generated_grouped_arithmetic_corresponds alpha (sourceBits mask index) hAlpha
  refine ⟨out, ?_, hOutCanonical, ?_⟩
  · unfold
      V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_grouped_binary_deferred_log8
    simp only [core.option.Option.unwrap, ofOption, bind_tc_ok, Std.lift]
    rw [hHighRun]
    simp only [bind_tc_ok]
    rw [hRowRun]
    simp only [bind_tc_ok, Std.lift]
    rw [hMaskRun]
    simp only [bind_tc_ok, Std.lift]
    rw [generated_arithmetic_eq_grouped]
    exact hArithmetic
  · simpa [mask, row] using hOutExact

#print axioms selected_nibble_lt16
#print axioms live_index_bounds
#print axioms nibble_sum_bit_expansion
#print axioms generated_grouped_arithmetic_corresponds
#print axioms generated_grouped_log8_corresponds

end V7CallerCurrentReleaseGroupedBinaryLog8
