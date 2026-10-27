import RPu_FIr_NativeArray
set_option autoImplicit false
namespace AspisR1.FIr_ArrayRead
open Aeneas Aeneas.Std Result

theorem slot {T : Type} {N : Usize} (a : Array T N) (i : Usize) (z : T)
    (run : Array.index_usize a i=ok z) : a.val[i.val]?=some z := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i x hx
    have same : x=z := Result.ok.inj run
    subst x
    exact hx

theorem member {T : Type} {N : Usize} (a : Array T N) (i : Usize) (z : T)
    (run : Array.index_usize a i=ok z) : z∈a.val :=
  List.mem_of_getElem? (slot a i z run)

#print axioms slot
#print axioms member
end AspisR1.FIr_ArrayRead
