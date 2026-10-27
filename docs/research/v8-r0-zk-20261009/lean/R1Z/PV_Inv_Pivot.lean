import R1Z.PV_Inv_Guard
import Mathlib.Data.List.Find
set_option autoImplicit false
namespace R1Z.PV_Inv_Pivot
variable {K : Type} [Field K] [DecidableEq K]

def pivot (xs : List K) : Option K := xs.find? (fun x => decide (x ≠ 0))

theorem selected_nonzero (xs : List K) (v : K) (h : pivot xs = some v) : v ≠ 0 := by
  have := List.find?_some h
  exact of_decide_eq_true this

theorem selected_inverse (xs : List K) (v : K) (h : pivot xs = some v) :
    PV_Inv_Guard.checkedInverse v = some v⁻¹ :=
  PV_Inv_Guard.nonzero_branch v (selected_nonzero xs v h)

#print axioms selected_nonzero
#print axioms selected_inverse
end R1Z.PV_Inv_Pivot
