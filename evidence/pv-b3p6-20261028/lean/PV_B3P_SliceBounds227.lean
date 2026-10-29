import PV_B3P_Slice194227
import PV_B3P_SelectIndex227
namespace PV_B3P_SliceBounds227
open Aeneas Aeneas.Std PV_B3P_SelectIndex227
set_option autoImplicit false

theorem cursor {start remaining len limit : Nat}
    (hs : start+remaining=len) (hr : 0<remaining) (hl : len≤limit) :
    start<len ∧ start+1≤len ∧ start+1≤limit := by omega

theorem pair_read {α β : Type} {n : Usize}
    (left : Array α n) (right : Array β n) (i : Usize) (hi : i.val<n.val) :
    (do
      let a ← Array.index_usize left i
      let b ← Array.index_usize right i
      .ok (a,b)) =
    Result.ok (left.val[i.val]'(by simpa only [left.property] using hi),
      right.val[i.val]'(by simpa only [right.property] using hi)) := by
  rw [index_value left i hi]
  simp only [bind_tc_ok]
  rw [index_value right i hi]
  rfl

#print axioms cursor
#print axioms pair_read
end PV_B3P_SliceBounds227
