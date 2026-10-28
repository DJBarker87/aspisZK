import Aeneas
set_option autoImplicit false
namespace AspisR1.NCI_GetterModel
open Aeneas Aeneas.Std Result

theorem array_get {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (hi : i.val<xs.val.length) :
    Array.index_usize xs i=ok (xs.val[i.val]'hi) := by
  unfold Array.index_usize
  change (match xs.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x)=ok (xs.val[i.val]'hi)
  rw [List.getElem?_eq_getElem hi]

theorem slice_get {α : Type} (xs : Slice α) (i : Usize)
    (hi : i.val<xs.val.length) :
    Slice.index_usize xs i=ok (xs.val[i.val]'hi) := by
  simp [Slice.index_usize,hi]
#print axioms array_get
#print axioms slice_get
end AspisR1.NCI_GetterModel
