import RPu_RowCallbackSlice
import ExtractedMaskReducerOps
import RPu_RawPoseidonExternalRows

/-!
Attempt to isolate the generated G closure-call arithmetic for output lane 0.
This is a proof draft only; the source/array graph and reducer are not yet
connected by a checked theorem. It uses G's generated names unchanged.
-/
set_option autoImplicit false
namespace AspisR1.RawPoseidonExternalRowClosure

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev Input := Array (Array Std.U32 4#usize) 4#usize
abbrev Closure := state_only_poseidon.external_linear_lazy_row.closure

private theorem widen_value (x : Std.U32) :
    (core.convert.num.FromU64U32.from x).val = x.val := by
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  apply BitVec.toNat_setWidth_of_le
  decide

/-- The output-0 arithmetic branch, with its four captured limbs already read
and widened exactly as the generated closure does. -/
def row0FromWide (a b c d : Std.U64) : Result Std.U64 := do
  let i5 ← 2#u64 * a
  let i6 ← 3#u64 * b
  let i7 ← i5 + i6
  let i8 ← i7 + c
  let i9 ← i8 + d
  ok i9

theorem row0FromWide_success (a b c d : Std.U64)
    (ha : a.val < 2^32) (hb : b.val < 2^32)
    (hc : c.val < 2^32) (hd : d.val < 2^32) :
    ∃ z : Std.U64, row0FromWide a b c d = .ok z ∧
      z.val = 2*a.val + 3*b.val + c.val + d.val := by
  have h5 : (2#u64).val * a.val < 2^64 := by
    change 2 * a.val < 2^64
    omega
  obtain ⟨i5, hi5, hv5⟩ := AspisR1.ExtractedMaskReducerOps.mul_success (2#u64) a h5
  have h6 : (3#u64).val * b.val < 2^64 := by
    change 3 * b.val < 2^64
    omega
  obtain ⟨i6, hi6, hv6⟩ := AspisR1.ExtractedMaskReducerOps.mul_success (3#u64) b h6
  rw [show (2#u64).val = 2 by decide] at hv5
  rw [show (3#u64).val = 3 by decide] at hv6
  have h7 : i5.val + i6.val < 2^64 := by rw [hv5, hv6]; omega
  obtain ⟨i7, hi7, hv7⟩ := AspisR1.ExtractedMaskReducerOps.add_success i5 i6 h7
  have h8 : i7.val + c.val < 2^64 := by rw [hv7]; omega
  obtain ⟨i8, hi8, hv8⟩ := AspisR1.ExtractedMaskReducerOps.add_success i7 c h8
  have h9 : i8.val + d.val < 2^64 := by rw [hv8]; omega
  obtain ⟨i9, hi9, hv9⟩ := AspisR1.ExtractedMaskReducerOps.add_success i8 d h9
  refine ⟨i9, ?_, ?_⟩
  · change (do
      let i5 ← UScalar.mul (2#u64) a
      let i6 ← UScalar.mul (3#u64) b
      let i7 ← UScalar.add i5 i6
      let i8 ← UScalar.add i7 c
      let i9 ← UScalar.add i8 d
      Result.ok i9) = Result.ok i9
    change UScalar.mul (2#u64) a = Result.ok i5 at hi5
    change UScalar.mul (3#u64) b = Result.ok i6 at hi6
    change UScalar.add i5 i6 = Result.ok i7 at hi7
    change UScalar.add i7 c = Result.ok i8 at hi8
    change UScalar.add i8 d = Result.ok i9 at hi9
    simp only [bind_tc_ok, hi5, hi6, hi7, hi8, hi9]
  · simpa only [hv5, hv6, hv7, hv8] using hv9

/-- The generated output-0 branch after its four indexed reads. The helper
keeps the exact conversion and operation order of G's `call_mut` body. -/
def row0FromU32 (a b c d : Std.U32) : Result Std.U64 := do
  let a64 ← lift (core.convert.num.FromU64U32.from a)
  let b64 ← lift (core.convert.num.FromU64U32.from b)
  let c64 ← lift (core.convert.num.FromU64U32.from c)
  let d64 ← lift (core.convert.num.FromU64U32.from d)
  row0FromWide a64 b64 c64 d64

theorem row0FromU32_success (a b c d : Std.U32) :
    ∃ z : Std.U64, row0FromU32 a b c d = .ok z ∧
      z.val = 2*a.val + 3*b.val + c.val + d.val := by
  have ha : a.val < 2^32 := by exact a.bv.isLt
  have hb : b.val < 2^32 := by exact b.bv.isLt
  have hc : c.val < 2^32 := by exact c.bv.isLt
  have hd : d.val < 2^32 := by exact d.bv.isLt
  obtain ⟨z, hz, hv⟩ := row0FromWide_success
    (core.convert.num.FromU64U32.from a)
    (core.convert.num.FromU64U32.from b)
    (core.convert.num.FromU64U32.from c)
    (core.convert.num.FromU64U32.from d)
    (by rw [widen_value]; exact ha) (by rw [widen_value]; exact hb)
    (by rw [widen_value]; exact hc) (by rw [widen_value]; exact hd)
  refine ⟨z, ?_, ?_⟩
  · simpa only [row0FromU32, row0FromWide, Aeneas.Std.lift, bind_tc_ok,
      hz]
  · simpa only [widen_value] using hv

/-- Output-lane 0 of the generated G closure call. The four indexed reads are
explicit; `hlimb` records the dynamic inner-array index range. -/
theorem call_mut_output0
    (input : Input) (limb : Std.Usize)
    (r0 r1 r2 r3 : Array Std.U32 4#usize)
    (x0 x1 x2 x3 : Std.U32)
    (hr0 : Array.index_usize input 0#usize = .ok r0)
    (hr1 : Array.index_usize input 1#usize = .ok r1)
    (hr2 : Array.index_usize input 2#usize = .ok r2)
    (hr3 : Array.index_usize input 3#usize = .ok r3)
    (hx0 : Array.index_usize r0 limb = .ok x0)
    (hx1 : Array.index_usize r1 limb = .ok x1)
    (hx2 : Array.index_usize r2 limb = .ok x2)
    (hx3 : Array.index_usize r3 limb = .ok x3)
    (hlimb : limb.val < 4) :
    ∃ z : Std.U64,
      state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (input, 0#usize) limb = .ok (z, (input, 0#usize)) ∧
      z.val = 2*x0.val + 3*x1.val + x2.val + x3.val := by
  obtain ⟨z, hz, hv⟩ := row0FromU32_success x0 x1 x2 x3
  refine ⟨z, ?_, hv⟩
  have hidx : (0#usize).val = 0 := by decide
  have hz' : (do
      let out ← row0FromU32 x0 x1 x2 x3
      (Result.ok (out, (input, 0#usize)) :
        Result (Std.U64 × state_only_poseidon.external_linear_lazy_row.closure))) =
      (Result.ok (z, (input, 0#usize)) :
        Result (Std.U64 × state_only_poseidon.external_linear_lazy_row.closure)) := by
    simp [hz, bind_tc_ok]
  simpa only [state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut,
    hr0, hr1, hr2, hr3, hx0, hx1, hx2, hx3, hidx,
    row0FromU32, row0FromWide, Aeneas.Std.lift, bind_tc_ok, bind_assoc_eq] using hz'

#print axioms row0FromWide_success
#print axioms row0FromU32_success
#print axioms call_mut_output0
end AspisR1.RawPoseidonExternalRowClosure
