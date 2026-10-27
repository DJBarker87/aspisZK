import FJc_ArrayRead
set_option autoImplicit false
namespace AspisR1.FJj_ArrayReadTotal
open Aeneas Aeneas.Std Result

theorem value {A : Type} {N : Usize} (a : Array A N) (i : Usize) (hi : i.val < N.val) :
    ∃ x,Array.index_usize a i=ok x := by
  have h : i.val < a.val.length := by rw [Array.length_eq];exact hi
  refine ⟨a.val[i.val],?_⟩
  unfold Array.index_usize
  change (match a.val[i.val]? with | none=>fail Error.arrayOutOfBounds | some x=>ok x)=_
  rw [List.getElem?_eq_getElem h]
#print axioms value
end AspisR1.FJj_ArrayReadTotal
