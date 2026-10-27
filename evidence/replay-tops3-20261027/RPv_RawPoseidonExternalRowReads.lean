import RPv_RawPoseidonExternalRowClosure

/-!
Wrapper that derives the successful outer and limb reads from the fixed-size
Aeneas Array representation. It stops at the generated output-0 callback and
records the raw natural row value; it says nothing about `from_fn` or `map`.
-/
set_option autoImplicit false
namespace AspisR1.RawPoseidonExternalRowReads

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.RawPoseidonExternalRowClosure

/-- Standard checked-index fact for Aeneas's list-backed fixed-size arrays. -/
theorem array_index_usize_ok {α : Type} {n : Std.Usize}
    (a : Aeneas.Std.Array α n) (i : Std.Usize) (hi : i.val < n.val) :
    Aeneas.Std.Array.index_usize a i =
      .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Aeneas.Std.Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

/-- The `j`th fixed row of the outer `[4][4]` input. -/
def rowValue (input : Input) (j : Fin 4) : Array Std.U32 4#usize :=
  input.val[j.val]'(by simpa [input.property] using j.isLt)

/-- The selected limb in row `j`; the bound is exactly the callback's
`tupled_args.val < 4` precondition. -/
def limbValue (input : Input) (j : Fin 4) (limb : Std.Usize)
    (hlimb : limb.val < 4) : Std.U32 :=
  (rowValue input j).val[limb.val]'(by
    have hlimb' : limb.val < (4#usize).val := by simpa using hlimb
    simpa [(rowValue input j).property] using hlimb')

/-- Raw U32-weighted value of callback output lane zero at one limb. -/
def rawRowNat (input : Input) (limb : Std.Usize) (hlimb : limb.val < 4) : Nat :=
  2 * (limbValue input ⟨0, by decide⟩ limb hlimb).val +
  3 * (limbValue input ⟨1, by decide⟩ limb hlimb).val +
      (limbValue input ⟨2, by decide⟩ limb hlimb).val +
      (limbValue input ⟨3, by decide⟩ limb hlimb).val

theorem call_mut_output0_of_array_bounds
    (input : Input) (limb : Std.Usize) (hlimb : limb.val < 4) :
    ∃ z : Std.U64,
      state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (input, 0#usize) limb = .ok (z, (input, 0#usize)) ∧
      z.val = rawRowNat input limb hlimb := by
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
    simpa [r0, rowValue, j0] using
      array_index_usize_ok input 0#usize (by decide)
  have hr1 : Array.index_usize input 1#usize = .ok r1 := by
    simpa [r1, rowValue, j1] using
      array_index_usize_ok input 1#usize (by decide)
  have hr2 : Array.index_usize input 2#usize = .ok r2 := by
    simpa [r2, rowValue, j2] using
      array_index_usize_ok input 2#usize (by decide)
  have hr3 : Array.index_usize input 3#usize = .ok r3 := by
    simpa [r3, rowValue, j3] using
      array_index_usize_ok input 3#usize (by decide)
  have hb : limb.val < (4#usize).val := by simpa using hlimb
  have hx0 : Array.index_usize r0 limb = .ok x0 := by
    simpa [x0, r0, limbValue, rowValue, j0] using
      array_index_usize_ok r0 limb hb
  have hx1 : Array.index_usize r1 limb = .ok x1 := by
    simpa [x1, r1, limbValue, rowValue, j1] using
      array_index_usize_ok r1 limb hb
  have hx2 : Array.index_usize r2 limb = .ok x2 := by
    simpa [x2, r2, limbValue, rowValue, j2] using
      array_index_usize_ok r2 limb hb
  have hx3 : Array.index_usize r3 limb = .ok x3 := by
    simpa [x3, r3, limbValue, rowValue, j3] using
      array_index_usize_ok r3 limb hb
  obtain ⟨z, hz, hv⟩ := call_mut_output0 input limb r0 r1 r2 r3 x0 x1 x2 x3
    hr0 hr1 hr2 hr3 hx0 hx1 hx2 hx3 hlimb
  refine ⟨z, hz, ?_⟩
  simpa [rawRowNat, x0, x1, x2, x3, limbValue, rowValue, j0, j1, j2, j3] using hv

#print axioms array_index_usize_ok
#print axioms call_mut_output0_of_array_bounds
end AspisR1.RawPoseidonExternalRowReads
