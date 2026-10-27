import KSC1_P7
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSC1.P7

theorem any_not_all {T : Type} (f : T → Result Bool) (xs : List T) :
    (do let b ← List.allM (fun x => do let b ← f x; ok (!b)) xs; ok (!b)) =
      List.anyM f xs := by
  induction xs with
  | nil => simp [List.allM, List.anyM] <;> rfl
  | cons x xs ih =>
    simp only [List.allM, List.anyM]
    cases h : f x with
    | fail e => simp [h]
    | div => simp [h]
    | ok b => cases b <;> simp [h, ih] <;> rfl

theorem slice_array_ne_p7 {T U : Type} {N : Usize}
    (cmp : core.cmp.PartialEq T U) (s : Slice T) (a : Array U N) :
    KSA_Isolated.Slice.Insts.CoreCmpPartialEqArray.ne cmp s a =
      core.slice.cmp.PartialEqSlice.ne cmp s a.to_slice := by
  rw [slice_array_ne]
  unfold core.slice.cmp.PartialEqSlice.eq core.slice.cmp.PartialEqSlice.ne
  split
  · simpa using any_not_all (fun (p : T × U) => cmp.ne p.1 p.2) (s.val.zip a.to_slice.val)
  · rfl

#print axioms any_not_all
#print axioms slice_array_ne_p7
end KSC1.P7
