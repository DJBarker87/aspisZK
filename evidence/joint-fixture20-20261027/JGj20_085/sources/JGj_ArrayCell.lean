import JGj_RawBounds
set_option autoImplicit false
namespace AspisR1.JGj_ArrayCell
open Aeneas Aeneas.Std
open FJb_TailCell (cell)
theorem set {T : Type} {N : Usize} (a : Array T N) (i : Usize) (v : T) (j : Fin N.val) :
    cell (a.set i v) j=if j.val=i.val then v else cell a j := by
  simp only [cell,Array.set_val_eq,List.getElem_set]
#print axioms set
end AspisR1.JGj_ArrayCell
