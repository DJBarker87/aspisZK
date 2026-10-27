import RPt_FJc_ArrayRead
set_option autoImplicit false
namespace AspisR1.FJc_ReadSlot
open Aeneas Aeneas.Std Result
theorem slot {A : Type} {N : Usize} (a : Array A N) (i : Usize) (x : A)
    (run : Array.index_usize a i=ok x) : a.val[i.val]?=some x := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i v hv
    cases Result.ok.inj run
    exact hv
#print axioms slot
end AspisR1.FJc_ReadSlot
