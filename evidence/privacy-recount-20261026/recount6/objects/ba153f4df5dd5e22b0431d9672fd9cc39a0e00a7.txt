import Aeneas
set_option autoImplicit false
noncomputable section
namespace PV_B1_ArrayRead
open Aeneas Aeneas.Std Result

theorem read {T : Type} {n : Usize} (values : Array T n) (i : Usize)
    (bound : i.val < values.val.length) :
    Array.index_usize values i = ok (values.val[i.val]'bound) := by
  simp only [Array.index_usize,Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem bound]

def get2 {T : Type} (values : Array T 2#usize) (i : Fin 2) : T :=
  values.val[i.val]'(by rw [values.property]; exact i.isLt)

theorem first {T : Type} (values : Array T 2#usize) :
    Array.index_usize values 0#usize = ok (get2 values 0) := by
  exact read values 0#usize (by rw [values.property]; decide)

theorem second {T : Type} (values : Array T 2#usize) :
    Array.index_usize values 1#usize = ok (get2 values 1) := by
  exact read values 1#usize (by rw [values.property]; decide)
#print axioms read
#print axioms first
#print axioms second
theorem slice_read {T : Type} (values : Slice T) (i : Usize)
    (bound : i.val < values.val.length) :
    Slice.index_usize values i = ok (values.val[i.val]'bound) := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem bound]

theorem array_fail {T : Type} {n : Usize} (xs : Array T n) (i : Usize)
    (h : n.val ≤ i.val) :
    Array.index_usize xs i = fail .arrayOutOfBounds := by
  change (match xs.val[i.val]? with | none => _ | some x => _) = _
  rw [List.getElem?_eq_none (by simpa only [xs.property] using h)]
#print axioms slice_read
#print axioms array_fail
end PV_B1_ArrayRead
