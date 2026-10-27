import R1Z.PV_CB3_StagedTotal
set_option autoImplicit false
namespace R1Z.PV_CB3_IndexFailure
open Aeneas Aeneas.Std Result

theorem array_fail {T : Type} {n : Usize} (xs : Array T n) (i : Usize)
    (h : n.val ≤ i.val) :
    Array.index_usize xs i = fail .arrayOutOfBounds := by
  change (match xs.val[i.val]? with | none => _ | some x => _) = _
  rw [List.getElem?_eq_none (by simpa only [xs.property] using h)]
#print axioms array_fail
end R1Z.PV_CB3_IndexFailure
