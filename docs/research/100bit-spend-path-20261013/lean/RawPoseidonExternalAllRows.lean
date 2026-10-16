import RawPoseidonExternalRowReads
import RawPoseidonExternalRowCalls

/-!
All four generated callback lanes at one limb, with the successful fixed-array
reads derived from dimensions. This composes only `call_mut`; it does not model
`core.array.from_fn`, the parent loop, or `Array.map`.
-/
set_option autoImplicit false
namespace AspisR1.RawPoseidonExternalAllRows

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.RawPoseidonExternalRowClosure
open AspisR1.RawPoseidonExternalRowLanes
open AspisR1.RawPoseidonExternalRowCalls
open AspisR1.RawPoseidonExternalRowReads

theorem call_mut_all_lanes_of_array_bounds
    (input : Input) (limb : Std.Usize) (hlimb : limb.val < 4) :
    ∃ z0 z1 z2 z3 : Std.U64,
      state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (input, 0#usize) limb = .ok (z0, (input, 0#usize)) ∧
      z0.val = rawRowNat input limb hlimb ∧
      state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (input, 1#usize) limb = .ok (z1, (input, 1#usize)) ∧
      z1.val = (limbValue input ⟨0, by decide⟩ limb hlimb).val +
        2*(limbValue input ⟨1, by decide⟩ limb hlimb).val +
        3*(limbValue input ⟨2, by decide⟩ limb hlimb).val +
          (limbValue input ⟨3, by decide⟩ limb hlimb).val ∧
      state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (input, 2#usize) limb = .ok (z2, (input, 2#usize)) ∧
      z2.val = (limbValue input ⟨0, by decide⟩ limb hlimb).val +
        (limbValue input ⟨1, by decide⟩ limb hlimb).val +
        2*(limbValue input ⟨2, by decide⟩ limb hlimb).val +
        3*(limbValue input ⟨3, by decide⟩ limb hlimb).val ∧
      state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (input, 3#usize) limb = .ok (z3, (input, 3#usize)) ∧
      z3.val = 3*(limbValue input ⟨0, by decide⟩ limb hlimb).val +
        (limbValue input ⟨1, by decide⟩ limb hlimb).val +
        (limbValue input ⟨2, by decide⟩ limb hlimb).val +
        2*(limbValue input ⟨3, by decide⟩ limb hlimb).val := by
  let j0 : Fin 4 := ⟨0, by decide⟩
  let j1 : Fin 4 := ⟨1, by decide⟩
  let j2 : Fin 4 := ⟨2, by decide⟩
  let j3 : Fin 4 := ⟨3, by decide⟩
  let r0 := rowValue input j0
  let r1 := rowValue input j1
  let r2 := rowValue input j2
  let r3 := rowValue input j3
  let x0 := limbValue input j0 limb hlimb
  let x1 := limbValue input j1 limb hlimb
  let x2 := limbValue input j2 limb hlimb
  let x3 := limbValue input j3 limb hlimb
  have hr0 : Array.index_usize input 0#usize = .ok r0 := by
    simpa [r0, rowValue, j0] using array_index_usize_ok input 0#usize (by decide)
  have hr1 : Array.index_usize input 1#usize = .ok r1 := by
    simpa [r1, rowValue, j1] using array_index_usize_ok input 1#usize (by decide)
  have hr2 : Array.index_usize input 2#usize = .ok r2 := by
    simpa [r2, rowValue, j2] using array_index_usize_ok input 2#usize (by decide)
  have hr3 : Array.index_usize input 3#usize = .ok r3 := by
    simpa [r3, rowValue, j3] using array_index_usize_ok input 3#usize (by decide)
  have hb : limb.val < (4#usize).val := by simpa using hlimb
  have hx0 : Array.index_usize r0 limb = .ok x0 := by
    simpa [x0, r0, limbValue, rowValue, j0] using array_index_usize_ok r0 limb hb
  have hx1 : Array.index_usize r1 limb = .ok x1 := by
    simpa [x1, r1, limbValue, rowValue, j1] using array_index_usize_ok r1 limb hb
  have hx2 : Array.index_usize r2 limb = .ok x2 := by
    simpa [x2, r2, limbValue, rowValue, j2] using array_index_usize_ok r2 limb hb
  have hx3 : Array.index_usize r3 limb = .ok x3 := by
    simpa [x3, r3, limbValue, rowValue, j3] using array_index_usize_ok r3 limb hb
  obtain ⟨z0, hc0, hv0⟩ := call_mut_output0 input limb r0 r1 r2 r3 x0 x1 x2 x3
    hr0 hr1 hr2 hr3 hx0 hx1 hx2 hx3 hlimb
  obtain ⟨z1, hc1, hv1⟩ := call_mut_output1 input limb r0 r1 r2 r3 x0 x1 x2 x3
    hr0 hr1 hr2 hr3 hx0 hx1 hx2 hx3 hlimb
  obtain ⟨z2, hc2, hv2⟩ := call_mut_output2 input limb r0 r1 r2 r3 x0 x1 x2 x3
    hr0 hr1 hr2 hr3 hx0 hx1 hx2 hx3 hlimb
  obtain ⟨z3, hc3, hv3⟩ := call_mut_output3 input limb r0 r1 r2 r3 x0 x1 x2 x3
    hr0 hr1 hr2 hr3 hx0 hx1 hx2 hx3 hlimb
  refine ⟨z0, z1, z2, z3, hc0, ?_, hc1, ?_, hc2, ?_, hc3, ?_⟩
  · simpa [rawRowNat, x0, x1, x2, x3, limbValue, rowValue, j0, j1, j2, j3] using hv0
  · simpa [x0, x1, x2, x3, limbValue, rowValue, j0, j1, j2, j3] using hv1
  · simpa [x0, x1, x2, x3, limbValue, rowValue, j0, j1, j2, j3] using hv2
  · simpa [x0, x1, x2, x3, limbValue, rowValue, j0, j1, j2, j3] using hv3

#print axioms call_mut_all_lanes_of_array_bounds
end AspisR1.RawPoseidonExternalAllRows
