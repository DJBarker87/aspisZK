import Aeneas.Std

set_option autoImplicit false
namespace AspisR1PoseidonPreparedChannelArraySet
open Aeneas.Std

def at3 {α : Type} (a : Array α 3#usize) (i : Usize) (hi : i.val < 3) : α :=
  a.val[i.val]'(by simpa [a.property] using hi)

theorem at3_set {α : Type} (a : Array α 3#usize) (i j : Usize)
    (x : α) (hi : i.val < 3) (hj : j.val < 3) :
    at3 (a.set i x) j hj = if j.val = i.val then x else at3 a j hj := by
  unfold at3
  by_cases heq : j.val = i.val
  · simp [Array.set_val_eq, heq]
  · have hne : i.val ≠ j.val := Ne.symm heq
    simp [Array.set_val_eq, List.getElem_set_ne, heq, hne]

#print axioms at3_set
end AspisR1PoseidonPreparedChannelArraySet
