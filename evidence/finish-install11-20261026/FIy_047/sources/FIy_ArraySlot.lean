import FIw_ArrayValue
set_option autoImplicit false
namespace AspisR1.FIy_ArraySlot
open Aeneas Aeneas.Std Result

theorem value {A : Type} {N : Usize} (a : Array A N) (i : Usize) (z : A)
    (run : Array.index_usize a i=ok z) : a.val[i.val]?=some z := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i x hx
    have same : x=z := Result.ok.inj run
    subst x
    exact hx
#print axioms value
end AspisR1.FIy_ArraySlot
