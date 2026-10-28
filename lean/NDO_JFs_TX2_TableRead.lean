import NDO_JFs_TX2_PointShift
set_option autoImplicit false
namespace AspisR1.JFs_TX2_TableRead
open Aeneas Aeneas.Std Result

theorem source {α : Type} {N : Usize} (a : Array α N) (i : Usize) (x : α)
    (selected : a.val[i.val]?=some x) : Array.index_usize a i=ok x := by
  unfold Array.index_usize
  change (match a.val[i.val]? with | none => _ | some y => ok y)=ok x
  rw [selected]

#print axioms source
end AspisR1.JFs_TX2_TableRead
