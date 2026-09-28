import V7CallerCurrentReleaseR26Qm31DotInnerIterator

/-!
# One generated three-lane raw QM31-dot component step

This file isolates the literal source body that updates the three Karatsuba
lanes for one CM31 pair.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31DotRawComponent

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotInnerIterator

abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev Pair := CM31 × CM31
abbrev Raw := Array Std.U64 9#usize

local instance : Inhabited Std.U64 := ⟨0#u64⟩
local instance : Inhabited CM31 :=
  ⟨{ a := field.M31.ZERO, b := field.M31.ZERO }⟩

def accumulateRawLane (raw : Raw) (index : Std.Usize)
    (left right : M31) : Raw :=
  raw.set index
    (Std.U64.wrapping_add raw.val[index.val]!
      (Std.U64.wrapping_mul (UScalar.cast .U64 left)
        (UScalar.cast .U64 right)))

def accumulateRawComponent (raw : Raw) (component : Std.Usize)
    (left right : CM31) (leftSum rightSum : M31) : Raw :=
  let offset := Std.Usize.wrapping_mul component 3#usize
  let raw0 := accumulateRawLane raw offset left.a right.a
  let raw1 := accumulateRawLane raw0
    (Std.Usize.wrapping_add offset 1#usize) left.b right.b
  accumulateRawLane raw1 (Std.Usize.wrapping_add offset 2#usize)
    leftSum rightSum

private theorem array_index_run {T : Type} [Inhabited T]
    {n : Std.Usize} (values : Array T n) (index : Std.Usize)
    (bound : index.val < values.length) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index bound)
  have listExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using bound
  simpa [exact, listExact] using run

private theorem array_update_to_set {T : Type}
    {n : Std.Usize} (values : Array T n) (index : Std.Usize)
    (value : T) (bound : index.val < n.val) :
    values.update index value = ok (values.set index value) := by
  obtain ⟨updated, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value (by
      simpa [Array.length_eq] using bound))
  subst updated
  exact run

private theorem component_offsets
    (component : Std.Usize) (componentBound : component.val < 3) :
    let offset := Std.Usize.wrapping_mul component 3#usize
    offset.val = component.val * 3 ∧
      (Std.Usize.wrapping_add offset 1#usize).val = component.val * 3 + 1 ∧
      (Std.Usize.wrapping_add offset 2#usize).val = component.val * 3 + 2 := by
  have nineSize : 9 < Usize.size := by
    have literalBound := UScalar.hSize (9#usize)
    simpa [UScalar.size_UScalarTyUsize] using literalBound
  dsimp only
  have mulBound : component.val * 3 < Usize.size := by omega
  have addOneBound : component.val * 3 + 1 < Usize.size := by omega
  have addTwoBound : component.val * 3 + 2 < Usize.size := by omega
  rw [Std.Usize.wrapping_mul_val_eq]
  norm_num
  rw [Nat.mod_eq_of_lt mulBound]
  constructor
  · rfl
  constructor
  · exact Nat.mod_eq_of_lt addOneBound
  · exact Nat.mod_eq_of_lt addTwoBound

/-- One active iteration of the literal generated three-pair loop performs
exactly the three array updates shown by `accumulateRawComponent`. -/
theorem generated_raw_component_body_step
    (pairs : Array Pair 3#usize) (raw : Raw) (processed : Nat)
    (active : processed < 3)
    (pairsCanonical : ∀ component, component < 3 →
      GeneratedCanonicalCM31 pairs.val[component]!.1 ∧
        GeneratedCanonicalCM31 pairs.val[component]!.2) :
    ∃ leftSum rightSum,
      field.qm31_dot_loop0_loop0_loop0.body
          (expectedPairIterator pairs processed) raw =
        ok (cont
          (expectedPairIterator pairs (processed + 1),
            accumulateRawComponent raw (usizeOfNatTruncate processed)
              pairs.val[processed]!.1 pairs.val[processed]!.2
              leftSum rightSum)) ∧
      field.M31.add pairs.val[processed]!.1.a
          pairs.val[processed]!.1.b = ok leftSum ∧
      field.M31.add pairs.val[processed]!.2.a
          pairs.val[processed]!.2.b = ok rightSum ∧
      GeneratedCanonicalM31 leftSum ∧ GeneratedCanonicalM31 rightSum ∧
      generatedM31ToExact leftSum =
        generatedM31ToExact pairs.val[processed]!.1.a +
          generatedM31ToExact pairs.val[processed]!.1.b ∧
      generatedM31ToExact rightSum =
        generatedM31ToExact pairs.val[processed]!.2.a +
          generatedM31ToExact pairs.val[processed]!.2.b := by
  let component := usizeOfNatTruncate processed
  have componentVal : component.val = processed :=
    usizeOfNatTruncate_val_eq (by
      exact small_fits_usize (by omega))
  obtain ⟨leftCanonical, rightCanonical⟩ :=
    pairsCanonical processed active
  obtain ⟨leftSum, leftSumRun, leftSumCanonical, leftSumExact⟩ :=
    generated_m31_add_corresponds pairs.val[processed]!.1.a
      pairs.val[processed]!.1.b leftCanonical.1 leftCanonical.2
  obtain ⟨rightSum, rightSumRun, rightSumCanonical, rightSumExact⟩ :=
    generated_m31_add_corresponds pairs.val[processed]!.2.a
      pairs.val[processed]!.2.b rightCanonical.1 rightCanonical.2
  obtain ⟨offsetVal, offsetOneVal, offsetTwoVal⟩ :=
    component_offsets component (by omega)
  let offset := Std.Usize.wrapping_mul component 3#usize
  let offsetOne := Std.Usize.wrapping_add offset 1#usize
  let offsetTwo := Std.Usize.wrapping_add offset 2#usize
  have offsetBound : offset.val < 9 := by rw [offsetVal]; omega
  have offsetOneBound : offsetOne.val < 9 := by rw [offsetOneVal]; omega
  have offsetTwoBound : offsetTwo.val < 9 := by rw [offsetTwoVal]; omega
  have rawRead0 := array_index_run raw offset (by
    simpa [Array.length_eq] using offsetBound)
  let product0 := Std.U64.wrapping_mul
    (UScalar.cast .U64 pairs.val[processed]!.1.a)
    (UScalar.cast .U64 pairs.val[processed]!.2.a)
  let value0 := Std.U64.wrapping_add raw.val[offset.val]! product0
  let raw0 := accumulateRawLane raw offset pairs.val[processed]!.1.a
    pairs.val[processed]!.2.a
  have rawUpdate0 : raw.update offset value0 = ok raw0 := by
    exact array_update_to_set raw offset value0 offsetBound
  have rawRead1 := array_index_run raw0 offsetOne (by
    simpa [Array.length_eq] using offsetOneBound)
  let product1 := Std.U64.wrapping_mul
    (UScalar.cast .U64 pairs.val[processed]!.1.b)
    (UScalar.cast .U64 pairs.val[processed]!.2.b)
  let value1 := Std.U64.wrapping_add raw0.val[offsetOne.val]! product1
  let raw1 := accumulateRawLane raw0 offsetOne pairs.val[processed]!.1.b
    pairs.val[processed]!.2.b
  have rawUpdate1 : raw0.update offsetOne value1 = ok raw1 := by
    exact array_update_to_set raw0 offsetOne value1 offsetOneBound
  have rawRead2 := array_index_run raw1 offsetTwo (by
    simpa [Array.length_eq] using offsetTwoBound)
  let product2 := Std.U64.wrapping_mul
    (UScalar.cast .U64 leftSum) (UScalar.cast .U64 rightSum)
  let value2 := Std.U64.wrapping_add raw1.val[offsetTwo.val]! product2
  let raw2 := accumulateRawLane raw1 offsetTwo leftSum rightSum
  have rawUpdate2 : raw1.update offsetTwo value2 = ok raw2 := by
    exact array_update_to_set raw1 offsetTwo value2 offsetTwoBound
  refine ⟨leftSum, rightSum, ?_, leftSumRun, rightSumRun,
    leftSumCanonical, rightSumCanonical, ?_, ?_⟩
  · unfold field.qm31_dot_loop0_loop0_loop0.body
    rw [expected_pair_iterator_next pairs processed active]
    simp only [bind_tc_ok]
    change
      (do
        let offset' ← lift (Std.Usize.wrapping_mul component 3#usize)
        let i1 ← lift (core.convert.num.FromU64U32.from
          pairs.val[processed]!.1.a)
        let i3 ← lift (core.convert.num.FromU64U32.from
          pairs.val[processed]!.2.a)
        let i4 ← lift (Std.U64.wrapping_mul i1 i3)
        let i5 ← Array.index_usize raw offset'
        let i6 ← lift (Std.U64.wrapping_add i5 i4)
        let raw' ← Array.update raw offset' i6
        let i8 ← lift (core.convert.num.FromU64U32.from
          pairs.val[processed]!.1.b)
        let i10 ← lift (core.convert.num.FromU64U32.from
          pairs.val[processed]!.2.b)
        let i11 ← lift (Std.U64.wrapping_mul i8 i10)
        let i12 ← lift (Std.Usize.wrapping_add offset' 1#usize)
        let i13 ← Array.index_usize raw' i12
        let i14 ← lift (Std.U64.wrapping_add i13 i11)
        let raw'' ← Array.update raw' i12 i14
        let m ← field.M31.add pairs.val[processed]!.1.a
          pairs.val[processed]!.1.b
        let i15 ← lift (core.convert.num.FromU64U32.from m)
        let m1 ← field.M31.add pairs.val[processed]!.2.a
          pairs.val[processed]!.2.b
        let i16 ← lift (core.convert.num.FromU64U32.from m1)
        let i17 ← lift (Std.U64.wrapping_mul i15 i16)
        let i18 ← lift (Std.Usize.wrapping_add offset' 2#usize)
        let i19 ← Array.index_usize raw'' i18
        let i20 ← lift (Std.U64.wrapping_add i19 i17)
        let out ← Array.update raw'' i18 i20
        ok (cont (expectedPairIterator pairs (processed + 1), out))) = _
    simp only [Std.lift, from_u64_u32_eq_cast, bind_tc_ok]
    rw [rawRead0]
    simp only [bind_tc_ok]
    change
      (do
        let raw' ← Array.update raw offset value0
        let i13 ← Array.index_usize raw' offsetOne
        let raw'' ← Array.update raw' offsetOne
          (Std.U64.wrapping_add i13 product1)
        let m ← field.M31.add pairs.val[processed]!.1.a
          pairs.val[processed]!.1.b
        let m1 ← field.M31.add pairs.val[processed]!.2.a
          pairs.val[processed]!.2.b
        let i19 ← Array.index_usize raw'' offsetTwo
        let out ← Array.update raw'' offsetTwo
          (Std.U64.wrapping_add i19
            (Std.U64.wrapping_mul (UScalar.cast .U64 m)
              (UScalar.cast .U64 m1)))
        ok (cont (expectedPairIterator pairs (processed + 1), out))) = _
    rw [rawUpdate0]
    simp only [bind_tc_ok]
    rw [rawRead1]
    simp only [bind_tc_ok]
    change
      (do
        let raw'' ← Array.update raw0 offsetOne value1
        let m ← field.M31.add pairs.val[processed]!.1.a
          pairs.val[processed]!.1.b
        let m1 ← field.M31.add pairs.val[processed]!.2.a
          pairs.val[processed]!.2.b
        let i19 ← Array.index_usize raw'' offsetTwo
        let out ← Array.update raw'' offsetTwo
          (Std.U64.wrapping_add i19
            (Std.U64.wrapping_mul (UScalar.cast .U64 m)
              (UScalar.cast .U64 m1)))
        ok (cont (expectedPairIterator pairs (processed + 1), out))) = _
    rw [rawUpdate1]
    simp only [bind_tc_ok]
    rw [leftSumRun, rightSumRun]
    simp only [bind_tc_ok]
    rw [rawRead2]
    simp only [bind_tc_ok]
    change
      (do
        let out ← Array.update raw1 offsetTwo value2
        ok (cont (expectedPairIterator pairs (processed + 1), out))) = _
    rw [rawUpdate2]
    simp [accumulateRawComponent, raw2, raw1, raw0, component, offset, offsetOne,
      offsetTwo, value0, value1, value2, product0, product1, product2,
      accumulateRawLane]
  · simpa [generatedM31ToExact] using leftSumExact
  · simpa [generatedM31ToExact] using rightSumExact

#print axioms generated_raw_component_body_step

end V7CallerCurrentReleaseR26Qm31DotRawComponent
