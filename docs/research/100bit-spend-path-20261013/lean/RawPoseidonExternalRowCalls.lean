import RowCallbackSlice
import ExtractedMaskReducerOps
import RawPoseidonExternalRows
import RawPoseidonExternalRowLanes

/-!
Generated G closure `call_mut` lane contracts. Each theorem assumes that all
four outer/inner array reads succeed and that the selected Usize index is below
4. No from_fn or parent Array.map behavior is included.
-/
set_option autoImplicit false
namespace AspisR1.RawPoseidonExternalRowCalls

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.RawPoseidonExternalRowClosure
open AspisR1.RawPoseidonExternalRowLanes

private theorem widen_value (x : Std.U32) :
    (core.convert.num.FromU64U32.from x).val = x.val := by
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  apply BitVec.toNat_setWidth_of_le
  decide

private def row1FromU32 (a b c d : Std.U32) : Result Std.U64 := do
  let a64 ← lift (core.convert.num.FromU64U32.from a)
  let b64 ← lift (core.convert.num.FromU64U32.from b)
  let c64 ← lift (core.convert.num.FromU64U32.from c)
  let d64 ← lift (core.convert.num.FromU64U32.from d)
  row1FromWide a64 b64 c64 d64

private theorem row1FromU32_success (a b c d : Std.U32) :
    ∃ z : Std.U64, row1FromU32 a b c d = .ok z ∧
      z.val = a.val + 2*b.val + 3*c.val + d.val := by
  have ha : a.val < 2^32 := a.bv.isLt
  have hb : b.val < 2^32 := b.bv.isLt
  have hc : c.val < 2^32 := c.bv.isLt
  have hd : d.val < 2^32 := d.bv.isLt
  obtain ⟨z, hz, hv⟩ := row1FromWide_success
    (core.convert.num.FromU64U32.from a)
    (core.convert.num.FromU64U32.from b)
    (core.convert.num.FromU64U32.from c)
    (core.convert.num.FromU64U32.from d)
    (by rw [widen_value]; exact ha) (by rw [widen_value]; exact hb)
    (by rw [widen_value]; exact hc) (by rw [widen_value]; exact hd)
  refine ⟨z, ?_, ?_⟩
  · simpa only [row1FromU32, row1FromWide, Aeneas.Std.lift, bind_tc_ok, hz]
  · simpa only [widen_value] using hv

private def row2FromU32 (a b c d : Std.U32) : Result Std.U64 := do
  let a64 ← lift (core.convert.num.FromU64U32.from a)
  let b64 ← lift (core.convert.num.FromU64U32.from b)
  let c64 ← lift (core.convert.num.FromU64U32.from c)
  let d64 ← lift (core.convert.num.FromU64U32.from d)
  row2FromWide a64 b64 c64 d64

private theorem row2FromU32_success (a b c d : Std.U32) :
    ∃ z : Std.U64, row2FromU32 a b c d = .ok z ∧
      z.val = a.val + b.val + 2*c.val + 3*d.val := by
  have ha : a.val < 2^32 := a.bv.isLt
  have hb : b.val < 2^32 := b.bv.isLt
  have hc : c.val < 2^32 := c.bv.isLt
  have hd : d.val < 2^32 := d.bv.isLt
  obtain ⟨z, hz, hv⟩ := row2FromWide_success
    (core.convert.num.FromU64U32.from a)
    (core.convert.num.FromU64U32.from b)
    (core.convert.num.FromU64U32.from c)
    (core.convert.num.FromU64U32.from d)
    (by rw [widen_value]; exact ha) (by rw [widen_value]; exact hb)
    (by rw [widen_value]; exact hc) (by rw [widen_value]; exact hd)
  refine ⟨z, ?_, ?_⟩
  · simpa only [row2FromU32, row2FromWide, Aeneas.Std.lift, bind_tc_ok, hz]
  · simpa only [widen_value] using hv

private def row3FromU32 (a b c d : Std.U32) : Result Std.U64 := do
  let a64 ← lift (core.convert.num.FromU64U32.from a)
  let b64 ← lift (core.convert.num.FromU64U32.from b)
  let c64 ← lift (core.convert.num.FromU64U32.from c)
  let d64 ← lift (core.convert.num.FromU64U32.from d)
  row3FromWide a64 b64 c64 d64

private theorem row3FromU32_success (a b c d : Std.U32) :
    ∃ z : Std.U64, row3FromU32 a b c d = .ok z ∧
      z.val = 3*a.val + b.val + c.val + 2*d.val := by
  have ha : a.val < 2^32 := a.bv.isLt
  have hb : b.val < 2^32 := b.bv.isLt
  have hc : c.val < 2^32 := c.bv.isLt
  have hd : d.val < 2^32 := d.bv.isLt
  obtain ⟨z, hz, hv⟩ := row3FromWide_success
    (core.convert.num.FromU64U32.from a)
    (core.convert.num.FromU64U32.from b)
    (core.convert.num.FromU64U32.from c)
    (core.convert.num.FromU64U32.from d)
    (by rw [widen_value]; exact ha) (by rw [widen_value]; exact hb)
    (by rw [widen_value]; exact hc) (by rw [widen_value]; exact hd)
  refine ⟨z, ?_, ?_⟩
  · simpa only [row3FromU32, row3FromWide, Aeneas.Std.lift, bind_tc_ok, hz]
  · simpa only [widen_value] using hv

theorem call_mut_output1
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
        (input, 1#usize) limb = .ok (z, (input, 1#usize)) ∧
      z.val = x0.val + 2*x1.val + 3*x2.val + x3.val := by
  have hgraph :
      state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (input, 1#usize) limb = (do
        let q0 ← Array.index_usize input 0#usize
        let x0 ← Array.index_usize q0 limb
        let q1 ← Array.index_usize input 1#usize
        let x1 ← Array.index_usize q1 limb
        let q2 ← Array.index_usize input 2#usize
        let x2 ← Array.index_usize q2 limb
        let q3 ← Array.index_usize input 3#usize
        let x3 ← Array.index_usize q3 limb
        let z ← row1FromU32 x0 x1 x2 x3
        ok (z, (input, 1#usize))) := by
    simp only [state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut,
      hr0, hr1, hr2, hr3, hx0, hx1, hx2, hx3,
      row1FromU32, row1FromWide, Aeneas.Std.lift, bind_tc_ok, bind_assoc_eq]
    rfl
  obtain ⟨z, hz, hv⟩ := row1FromU32_success x0 x1 x2 x3
  refine ⟨z, ?_, hv⟩
  rw [hgraph]
  simp only [hr0, hr1, hr2, hr3, hx0, hx1, hx2, hx3, hz, bind_tc_ok]

theorem call_mut_output2
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
        (input, 2#usize) limb = .ok (z, (input, 2#usize)) ∧
      z.val = x0.val + x1.val + 2*x2.val + 3*x3.val := by
  have hgraph :
      state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (input, 2#usize) limb = (do
        let q0 ← Array.index_usize input 0#usize
        let x0 ← Array.index_usize q0 limb
        let q1 ← Array.index_usize input 1#usize
        let x1 ← Array.index_usize q1 limb
        let q2 ← Array.index_usize input 2#usize
        let x2 ← Array.index_usize q2 limb
        let q3 ← Array.index_usize input 3#usize
        let x3 ← Array.index_usize q3 limb
        let z ← row2FromU32 x0 x1 x2 x3
        ok (z, (input, 2#usize))) := by
    simp only [state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut,
      hr0, hr1, hr2, hr3, hx0, hx1, hx2, hx3,
      row2FromU32, row2FromWide, Aeneas.Std.lift, bind_tc_ok, bind_assoc_eq]
    rfl
  obtain ⟨z, hz, hv⟩ := row2FromU32_success x0 x1 x2 x3
  refine ⟨z, ?_, hv⟩
  rw [hgraph]
  simp only [hr0, hr1, hr2, hr3, hx0, hx1, hx2, hx3, hz, bind_tc_ok]

theorem call_mut_output3
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
        (input, 3#usize) limb = .ok (z, (input, 3#usize)) ∧
      z.val = 3*x0.val + x1.val + x2.val + 2*x3.val := by
  have hgraph :
      state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (input, 3#usize) limb = (do
        let q0 ← Array.index_usize input 0#usize
        let x0 ← Array.index_usize q0 limb
        let q1 ← Array.index_usize input 1#usize
        let x1 ← Array.index_usize q1 limb
        let q2 ← Array.index_usize input 2#usize
        let x2 ← Array.index_usize q2 limb
        let q3 ← Array.index_usize input 3#usize
        let x3 ← Array.index_usize q3 limb
        let z ← row3FromU32 x0 x1 x2 x3
        ok (z, (input, 3#usize))) := by
    simp only [state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut,
      hr0, hr1, hr2, hr3, hx0, hx1, hx2, hx3,
      row3FromU32, row3FromWide, Aeneas.Std.lift, bind_tc_ok, bind_assoc_eq]
    rfl
  obtain ⟨z, hz, hv⟩ := row3FromU32_success x0 x1 x2 x3
  refine ⟨z, ?_, hv⟩
  rw [hgraph]
  simp only [hr0, hr1, hr2, hr3, hx0, hx1, hx2, hx3, hz, bind_tc_ok]

#print axioms call_mut_output1
#print axioms call_mut_output2
#print axioms call_mut_output3
end AspisR1.RawPoseidonExternalRowCalls
