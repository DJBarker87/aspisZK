import V7CallerCurrentReleaseR26Qm31DotRawComponent

/-!
# Exact semantics of one raw QM31-dot component update

The generated body updates three distinct lanes.  This file proves their
ordinary-natural-number meaning under explicit U64 bounds and records that all
other lanes are unchanged.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31DotRawComponentSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotRawArithmetic
open V7CallerCurrentReleaseR26Qm31DotInnerIterator
open V7CallerCurrentReleaseR26Qm31DotRawComponent

abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev Raw := Array Std.U64 9#usize

local instance : Inhabited Std.U64 := ⟨0#u64⟩

private theorem set_same {T : Type} [Inhabited T]
    {n : Std.Usize} (values : Array T n) (index : Std.Usize)
    (value : T) (bound : index.val < n.val) :
    (values.set index value).val[index.val]! = value := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_eq
  exact ⟨by simpa [Array.length_eq] using bound, rfl⟩

private theorem set_ne {T : Type} [Inhabited T]
    {n : Std.Usize} (values : Array T n) (index : Std.Usize)
    (value : T) (other : Nat) (different : other ≠ index.val) :
    (values.set index value).val[other]! = values.val[other]! := by
  apply List.set_getElem!_ne
  omega

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
  exact ⟨rfl, Nat.mod_eq_of_lt addOneBound,
    Nat.mod_eq_of_lt addTwoBound⟩

/-- The three writes made for one component are exact U64 additions, and the
remaining six lanes are framed. -/
theorem accumulate_raw_component_exact
    (raw : Raw) (component : Std.Usize) (left right : CM31)
    (leftSum rightSum : M31)
    (componentBound : component.val < 3)
    (leftCanonical : GeneratedCanonicalCM31 left)
    (rightCanonical : GeneratedCanonicalCM31 right)
    (leftSumCanonical : GeneratedCanonicalM31 leftSum)
    (rightSumCanonical : GeneratedCanonicalM31 rightSum)
    (bound0 : raw.val[component.val * 3]!.val +
      rawM31Product left.a right.a < 2 ^ 64)
    (bound1 : raw.val[component.val * 3 + 1]!.val +
      rawM31Product left.b right.b < 2 ^ 64)
    (bound2 : raw.val[component.val * 3 + 2]!.val +
      rawM31Product leftSum rightSum < 2 ^ 64) :
    let out := accumulateRawComponent raw component left right leftSum rightSum
    out.val[component.val * 3]!.val =
        raw.val[component.val * 3]!.val + rawM31Product left.a right.a ∧
      out.val[component.val * 3 + 1]!.val =
        raw.val[component.val * 3 + 1]!.val + rawM31Product left.b right.b ∧
      out.val[component.val * 3 + 2]!.val =
        raw.val[component.val * 3 + 2]!.val +
          rawM31Product leftSum rightSum ∧
      ∀ lane, lane < 9 →
        lane ≠ component.val * 3 →
        lane ≠ component.val * 3 + 1 →
        lane ≠ component.val * 3 + 2 →
        out.val[lane]! = raw.val[lane]! := by
  obtain ⟨offsetVal, offsetOneVal, offsetTwoVal⟩ :=
    component_offsets component componentBound
  let offset := Std.Usize.wrapping_mul component 3#usize
  let offsetOne := Std.Usize.wrapping_add offset 1#usize
  let offsetTwo := Std.Usize.wrapping_add offset 2#usize
  have offsetBound : offset.val < 9 := by rw [offsetVal]; omega
  have offsetOneBound : offsetOne.val < 9 := by rw [offsetOneVal]; omega
  have offsetTwoBound : offsetTwo.val < 9 := by rw [offsetTwoVal]; omega
  let value0 := Std.U64.wrapping_add raw.val[offset.val]!
    (Std.U64.wrapping_mul (UScalar.cast .U64 left.a)
      (UScalar.cast .U64 right.a))
  let raw0 := raw.set offset value0
  let value1 := Std.U64.wrapping_add raw0.val[offsetOne.val]!
    (Std.U64.wrapping_mul (UScalar.cast .U64 left.b)
      (UScalar.cast .U64 right.b))
  let raw1 := raw0.set offsetOne value1
  let value2 := Std.U64.wrapping_add raw1.val[offsetTwo.val]!
    (Std.U64.wrapping_mul (UScalar.cast .U64 leftSum)
      (UScalar.cast .U64 rightSum))
  let out := raw1.set offsetTwo value2
  have raw0At0 : raw0.val[offset.val]! = value0 :=
    set_same raw offset value0 offsetBound
  have raw0At1 : raw0.val[offsetOne.val]! = raw.val[offsetOne.val]! :=
    set_ne raw offset value0 offsetOne.val (by rw [offsetVal, offsetOneVal]; omega)
  have raw1At0 : raw1.val[offset.val]! = value0 := by
    rw [set_ne raw0 offsetOne value1 offset.val (by
      rw [offsetVal, offsetOneVal]; omega), raw0At0]
  have raw1At1 : raw1.val[offsetOne.val]! = value1 :=
    set_same raw0 offsetOne value1 offsetOneBound
  have raw1At2 : raw1.val[offsetTwo.val]! = raw.val[offsetTwo.val]! := by
    rw [set_ne raw0 offsetOne value1 offsetTwo.val (by
      rw [offsetOneVal, offsetTwoVal]; omega)]
    exact set_ne raw offset value0 offsetTwo.val (by
      rw [offsetVal, offsetTwoVal]; omega)
  have outAt0 : out.val[offset.val]! = value0 := by
    rw [set_ne raw1 offsetTwo value2 offset.val (by
      rw [offsetVal, offsetTwoVal]; omega), raw1At0]
  have outAt1 : out.val[offsetOne.val]! = value1 := by
    rw [set_ne raw1 offsetTwo value2 offsetOne.val (by
      rw [offsetOneVal, offsetTwoVal]; omega), raw1At1]
  have outAt2 : out.val[offsetTwo.val]! = value2 :=
    set_same raw1 offsetTwo value2 offsetTwoBound
  have value0Exact : value0.val = raw.val[offset.val]!.val +
      rawM31Product left.a right.a := by
    exact wrapping_accumulate_exact raw.val[offset.val]! left.a right.a
      leftCanonical.1 rightCanonical.1 (by
        rw [offsetVal]
        exact bound0)
  have value1Exact : value1.val = raw.val[offsetOne.val]!.val +
      rawM31Product left.b right.b := by
    change (Std.U64.wrapping_add raw0.val[offsetOne.val]!
      (Std.U64.wrapping_mul (UScalar.cast .U64 left.b)
        (UScalar.cast .U64 right.b))).val = _
    rw [raw0At1]
    exact wrapping_accumulate_exact raw.val[offsetOne.val]! left.b right.b
      leftCanonical.2 rightCanonical.2 (by
        rw [offsetOneVal]
        exact bound1)
  have value2Exact : value2.val = raw.val[offsetTwo.val]!.val +
      rawM31Product leftSum rightSum := by
    change (Std.U64.wrapping_add raw1.val[offsetTwo.val]!
      (Std.U64.wrapping_mul (UScalar.cast .U64 leftSum)
        (UScalar.cast .U64 rightSum))).val = _
    rw [raw1At2]
    exact wrapping_accumulate_exact raw.val[offsetTwo.val]! leftSum rightSum
      leftSumCanonical rightSumCanonical (by
        rw [offsetTwoVal]
        exact bound2)
  have localExact :
      out.val[offset.val]!.val = raw.val[offset.val]!.val +
          rawM31Product left.a right.a ∧
        out.val[offsetOne.val]!.val = raw.val[offsetOne.val]!.val +
          rawM31Product left.b right.b ∧
        out.val[offsetTwo.val]!.val = raw.val[offsetTwo.val]!.val +
          rawM31Product leftSum rightSum ∧
        ∀ lane, lane < 9 → lane ≠ offset.val → lane ≠ offsetOne.val →
          lane ≠ offsetTwo.val → out.val[lane]! = raw.val[lane]! := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [outAt0]
      exact value0Exact
    · rw [outAt1]
      exact value1Exact
    · rw [outAt2]
      exact value2Exact
    · intro lane laneBound different0 different1 different2
      rw [set_ne raw1 offsetTwo value2 lane different2,
        set_ne raw0 offsetOne value1 lane different1,
        set_ne raw offset value0 lane different0]
  have offsetOneFromOffset : offsetOne.val = offset.val + 1 := by
    rw [offsetOneVal, offsetVal]
  have offsetTwoFromOffset : offsetTwo.val = offset.val + 2 := by
    rw [offsetTwoVal, offsetVal]
  dsimp only
  rw [← offsetVal, ← offsetOneFromOffset, ← offsetTwoFromOffset]
  simpa only [out, raw1, raw0, value0, value1, value2,
    accumulateRawComponent, accumulateRawLane, offset, offsetOne, offsetTwo]
    using localExact

#print axioms accumulate_raw_component_exact

end V7CallerCurrentReleaseR26Qm31DotRawComponentSemantics
