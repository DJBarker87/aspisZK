import R1Z.PV_PoleLeafCorrect
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_ArrayReadValue
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
end R1Z.PV_ArrayReadValue
