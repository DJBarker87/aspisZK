import Aeneas.Std
/-! The retained sampler uses only this array lemma from the unrelated
mask-Horner proof cone. Copy the identical small API proof to avoid importing
or rebuilding that unrelated cone. -/
set_option autoImplicit false
namespace NDH_ArrayIndex
open Aeneas Aeneas.Std Result

theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Aeneas.Std.Array α n) (i : Usize) (hi : i.val < n.val) :
    Aeneas.Std.Array.index_usize a i =
      .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Aeneas.Std.Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]
#print axioms array_index_usize_ok
end NDH_ArrayIndex
