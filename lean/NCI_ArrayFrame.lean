import Aeneas
set_option autoImplicit false
namespace AspisR1.NCI_ArrayFrame
open Aeneas Aeneas.Std Result

theorem write {α : Type} {n : Usize} (xs : Array α n) (i : Usize) (value : α)
    (hi : i.val<xs.val.length) :
    ∃ out : Array α n, Array.update xs i value=ok out ∧ out.val=xs.val.set i.val value := by
  have lookup : xs[i]?=some (xs.val[i.val]'hi) := by
    change xs.val[i.val]?=some (xs.val[i.val]'hi)
    exact List.getElem?_eq_getElem hi
  refine ⟨⟨xs.val.set i.val value,by simpa using xs.property⟩,?_,rfl⟩
  simp only [Array.update,lookup]
#print axioms write
end AspisR1.NCI_ArrayFrame
