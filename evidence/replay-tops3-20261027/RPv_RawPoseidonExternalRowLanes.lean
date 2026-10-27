import RPv_RawPoseidonExternalRowClosure

/-!
Proof drafts for generated G callback lanes 1–3. These retain the generated
operation order and depend on the lane-0 helper module; they do not prove the
`from_fn` row or the parent `Array.map`.
-/
set_option autoImplicit false
namespace AspisR1.RawPoseidonExternalRowLanes

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.RawPoseidonExternalRowClosure

/-- Generated lane 1 arithmetic after widening its four U32 reads. -/
def row1FromWide (a b c d : Std.U64) : Result Std.U64 := do
  let i5 ← 2#u64 * b
  let i6 ← a + i5
  let i7 ← 3#u64 * c
  let i8 ← i6 + i7
  let i9 ← i8 + d
  ok i9

theorem row1FromWide_success (a b c d : Std.U64)
    (ha : a.val < 2^32) (hb : b.val < 2^32)
    (hc : c.val < 2^32) (hd : d.val < 2^32) :
    ∃ z : Std.U64, row1FromWide a b c d = .ok z ∧
      z.val = a.val + 2*b.val + 3*c.val + d.val := by
  have h5 : (2#u64).val * b.val < 2^64 := by
    change 2 * b.val < 2^64
    omega
  obtain ⟨i5, hi5, hv5⟩ := AspisR1.ExtractedMaskReducerOps.mul_success (2#u64) b h5
  change UScalar.mul (2#u64) b = Result.ok i5 at hi5
  rw [show (2#u64).val = 2 by rfl] at hv5
  have h6 : a.val + i5.val < 2^64 := by
    rw [hv5]
    omega
  obtain ⟨i6, hi6, hv6⟩ := AspisR1.ExtractedMaskReducerOps.add_success a i5 h6
  change UScalar.add a i5 = Result.ok i6 at hi6
  have h7 : (3#u64).val * c.val < 2^64 := by
    change 3 * c.val < 2^64
    omega
  obtain ⟨i7, hi7, hv7⟩ := AspisR1.ExtractedMaskReducerOps.mul_success (3#u64) c h7
  change UScalar.mul (3#u64) c = Result.ok i7 at hi7
  rw [show (3#u64).val = 3 by rfl] at hv7
  have h8 : i6.val + i7.val < 2^64 := by rw [hv6, hv7]; omega
  obtain ⟨i8, hi8, hv8⟩ := AspisR1.ExtractedMaskReducerOps.add_success i6 i7 h8
  change UScalar.add i6 i7 = Result.ok i8 at hi8
  have h9 : i8.val + d.val < 2^64 := by rw [hv8]; omega
  obtain ⟨i9, hi9, hv9⟩ := AspisR1.ExtractedMaskReducerOps.add_success i8 d h9
  change UScalar.add i8 d = Result.ok i9 at hi9
  refine ⟨i9, ?_, ?_⟩
  · change (do
      let i5 ← UScalar.mul (2#u64) b
      let i6 ← UScalar.add a i5
      let i7 ← UScalar.mul (3#u64) c
      let i8 ← UScalar.add i6 i7
      let i9 ← UScalar.add i8 d
      Result.ok i9) = Result.ok i9
    simp only [bind_tc_ok, hi5, hi6, hi7, hi8, hi9]
  · omega

/-- Generated lane 2 arithmetic after widening its four U32 reads. -/
def row2FromWide (a b c d : Std.U64) : Result Std.U64 := do
  let i5 ← a + b
  let i6 ← 2#u64 * c
  let i7 ← i5 + i6
  let i8 ← 3#u64 * d
  let i9 ← i7 + i8
  ok i9

theorem row2FromWide_success (a b c d : Std.U64)
    (ha : a.val < 2^32) (hb : b.val < 2^32)
    (hc : c.val < 2^32) (hd : d.val < 2^32) :
    ∃ z : Std.U64, row2FromWide a b c d = .ok z ∧
      z.val = a.val + b.val + 2*c.val + 3*d.val := by
  have h5 : a.val + b.val < 2^64 := by omega
  obtain ⟨i5, hi5, hv5⟩ := AspisR1.ExtractedMaskReducerOps.add_success a b h5
  change UScalar.add a b = Result.ok i5 at hi5
  have h6 : (2#u64).val * c.val < 2^64 := by
    change 2 * c.val < 2^64
    omega
  obtain ⟨i6, hi6, hv6⟩ := AspisR1.ExtractedMaskReducerOps.mul_success (2#u64) c h6
  change UScalar.mul (2#u64) c = Result.ok i6 at hi6
  rw [show (2#u64).val = 2 by rfl] at hv6
  have h7 : i5.val + i6.val < 2^64 := by rw [hv5, hv6]; omega
  obtain ⟨i7, hi7, hv7⟩ := AspisR1.ExtractedMaskReducerOps.add_success i5 i6 h7
  change UScalar.add i5 i6 = Result.ok i7 at hi7
  have h8 : (3#u64).val * d.val < 2^64 := by
    change 3 * d.val < 2^64
    omega
  obtain ⟨i8, hi8, hv8⟩ := AspisR1.ExtractedMaskReducerOps.mul_success (3#u64) d h8
  change UScalar.mul (3#u64) d = Result.ok i8 at hi8
  rw [show (3#u64).val = 3 by rfl] at hv8
  have h9 : i7.val + i8.val < 2^64 := by rw [hv7, hv8]; omega
  obtain ⟨i9, hi9, hv9⟩ := AspisR1.ExtractedMaskReducerOps.add_success i7 i8 h9
  change UScalar.add i7 i8 = Result.ok i9 at hi9
  refine ⟨i9, ?_, ?_⟩
  · change (do
      let i5 ← UScalar.add a b
      let i6 ← UScalar.mul (2#u64) c
      let i7 ← UScalar.add i5 i6
      let i8 ← UScalar.mul (3#u64) d
      let i9 ← UScalar.add i7 i8
      Result.ok i9) = Result.ok i9
    simp only [bind_tc_ok, hi5, hi6, hi7, hi8, hi9]
  · omega

/-- Generated lane 3 arithmetic after widening its four U32 reads. -/
def row3FromWide (a b c d : Std.U64) : Result Std.U64 := do
  let i5 ← 3#u64 * a
  let i6 ← i5 + b
  let i7 ← i6 + c
  let i8 ← 2#u64 * d
  let i9 ← i7 + i8
  ok i9

theorem row3FromWide_success (a b c d : Std.U64)
    (ha : a.val < 2^32) (hb : b.val < 2^32)
    (hc : c.val < 2^32) (hd : d.val < 2^32) :
    ∃ z : Std.U64, row3FromWide a b c d = .ok z ∧
      z.val = 3*a.val + b.val + c.val + 2*d.val := by
  have h5 : (3#u64).val * a.val < 2^64 := by
    change 3 * a.val < 2^64
    omega
  obtain ⟨i5, hi5, hv5⟩ := AspisR1.ExtractedMaskReducerOps.mul_success (3#u64) a h5
  change UScalar.mul (3#u64) a = Result.ok i5 at hi5
  rw [show (3#u64).val = 3 by rfl] at hv5
  have h6 : i5.val + b.val < 2^64 := by rw [hv5]; omega
  obtain ⟨i6, hi6, hv6⟩ := AspisR1.ExtractedMaskReducerOps.add_success i5 b h6
  change UScalar.add i5 b = Result.ok i6 at hi6
  have h7 : i6.val + c.val < 2^64 := by rw [hv6]; omega
  obtain ⟨i7, hi7, hv7⟩ := AspisR1.ExtractedMaskReducerOps.add_success i6 c h7
  change UScalar.add i6 c = Result.ok i7 at hi7
  have h8 : (2#u64).val * d.val < 2^64 := by
    change 2 * d.val < 2^64
    omega
  obtain ⟨i8, hi8, hv8⟩ := AspisR1.ExtractedMaskReducerOps.mul_success (2#u64) d h8
  change UScalar.mul (2#u64) d = Result.ok i8 at hi8
  rw [show (2#u64).val = 2 by rfl] at hv8
  have h9 : i7.val + i8.val < 2^64 := by rw [hv7, hv8]; omega
  obtain ⟨i9, hi9, hv9⟩ := AspisR1.ExtractedMaskReducerOps.add_success i7 i8 h9
  change UScalar.add i7 i8 = Result.ok i9 at hi9
  refine ⟨i9, ?_, ?_⟩
  · change (do
      let i5 ← UScalar.mul (3#u64) a
      let i6 ← UScalar.add i5 b
      let i7 ← UScalar.add i6 c
      let i8 ← UScalar.mul (2#u64) d
      let i9 ← UScalar.add i7 i8
      Result.ok i9) = Result.ok i9
    simp only [bind_tc_ok, hi5, hi6, hi7, hi8, hi9]
  · omega

#print axioms row1FromWide_success
#print axioms row2FromWide_success
#print axioms row3FromWide_success
end AspisR1.RawPoseidonExternalRowLanes
